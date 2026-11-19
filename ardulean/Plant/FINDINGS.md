# Findings

**F1. `sim/check_constants.py` does not check the plant constants.** It re-flies Monte Carlo starts and checks the
constants of the archived `Contracts/Mission/Sub.lean`; no script in `sim/` reads `Plant/Model/Constants.lean`. The
plant's check is `tests/plant/check_constants.py` (reads only, 0.03 s). For the X500 it compares every literal exactly
(as fractions of the decimal strings) with `sim/world/x500/x500.urdf`, `sim/world/airframes.py` (`LAG`),
`sim/run_copter.py` (`GRAVITY_MSS`, `CTRL_HZ`) and `sim/gorge_lockstep.py` (`--pyb-hz`, `substeps`), checks the four
propeller links at `(±0.174, ±0.174, 0.06)`, the URDF header's derivations, and the derived values: all agree
(`MAX_RPM = 9549.2965855` rpm `= 1000` rad/s, `fmax = 8.54858` N, `km/kf = 0.016` m, `amax = 16.564546` m/s², hover
fraction `0.592026`).

**F2. Line numbers of the sources drift.** The docstrings cite file and line as of 2026-11-16. While writing the X500
constants, three citations were corrected against the files before the model was frozen: the housekeeping's
`p.setGravity` is at `sim/world/gorge_aviary.py:49`, the `loadURDF` with `URDF_USE_INERTIA_FROM_FILE` at `:53-55`,
and `BaseAviary._physics` spans `gpd/envs/BaseAviary.py:676-707` (`forces` and `torques` at `:690-691`, the yaw sum at
`:694`).

**F3. Vehicle ratios hard-coded as literals (resolved).** The earlier plant had the gyroscopic coefficient and
`Jz/Jx` of its vehicle as numeric literals (`gyro`, and inside `Cd`), so the gyroscopic bounds would have been false
for other inertias. Now `gyro = (Jz - Jx)/Jx` and `Cd` uses `Jz / Jx`; the bounds `|Jz - Jy|/Jx, |Jx - Jz|/Jy,
|Jy - Jx|/Jz ≤ gyro` are proved from `Jy = Jx ≤ Jz` (`abs_gyroX_le` …), and every use of the vehicle's numbers outside
`Constants.lean` and `Step/Numbers.lean` goes through the named facts `Jy_eq_Jx`, `Jx_le_Jz`, `kmkf_Jx_le_lever_Jz`,
`one_le_thrust2weight`, `tauUp_lt_tauDown`. The audit's earlier rule-3 violations (`Cd_nonneg`, `Cd_mono`, `Katt_pos`)
are now counted "through a derived definition".

**F4. The first port needed no lemma renames.** (Lean 4.36-rc2 to 4.35 with the module system.) The X500 port kept
every theorem name but one (`OPEN.md`).

**F5. The joint sensitivity bound is loose away from the origin.** `norm_step_sub_step_le_exp` uses the Lipschitz
constant `K = Klip (box r)` of the whole field on the ball of radius `box r`, and `‖x‖` includes the position.
Evaluated for the X500 (Python, not in Lean), with the lag's `1/tauUp = 80` in `K`: `r = 1`: `box ≈ 3.33`,
`K ≈ 1548`, `e^{K h} ≈ 48`, input factor `(1/tauUp)(e^{Kh} - 1)/K ≈ 2.4` per unit command; `r = 2`: `e^{Kh} ≈ 2.6e4`,
factor `≈ 508`; `r = 5`: `e^{Kh} ≈ 4e21`. The sharp block-wise bound (`step_input_sens`, F8) replaces it for the
command: `0.0650` rad/s and `3.91e-3` m/s per unit command at any position.

**F6. Numerical check of the statements** (`tests/plant/numcheck.py` part (a), RK4 at `h/2000`, 20 random states with
unit quaternion, rates up to 3 rad/s, thrusts in `[0, 1]`, commands in `[-0.2, 1.2]⁴`; 2 s): the motor closed form and
three simulator updates agree with RK4 to `4e-15`; the thrust range and monotone approach hold; `‖q‖²` constant to
`5e-15`; the thrust sensitivities attain their constants `0.181269` and `0.904837`; hover is a rest point; every block
of `traj_input_sens` holds at 20 times per period (largest ratio actual/bound: thrust 1.000, rates 0.394, quaternion
0.107, velocity 0.400, position 0.400); `traj_pv_sharp`'s remainders are at most 0.208 of their bounds; level flight
over 40 periods and the spin closed form agree with RK4 to `1e-11`; the deviations from free fall reach their bounds to six
digits (over one period the down axis hardly turns); the evaluated constants of `Step/Numbers.lean` hold. No statement failed.

**F7. The model against the simulator** (`numcheck.py` part (b), `AirframeAviary` with the X500 URDF and the lag,
free flight 20 m up, PyBullet damping removed, same start and held commands; simulator − ODE). Hover: zero (`2e-17`).
Thrusts: agree to `4e-15` at every period (the simulator's lag is the exact step response, `step_fI_sim`). After one
period, over six scenarios (hover, roll, pitch and yaw command steps of 0.05, a general tilted moving state, a
torque-free tumble): `|Δp| ≤ 3.3e-6` m, `|Δv| ≤ 3.7e-5` m/s, attitude `≤ 5.2e-6` rad, `|Δω| ≤ 1.3e-3` rad/s; after 8
periods `≤ 2.6e-5` m, `2.6e-4` m/s, `1.6e-4` rad, `6.3e-3` rad/s; after 40 periods (0.1 s) `≤ 1.2e-4` m, `1.4e-3` m/s,
`1.6e-3` rad, `6.9e-3` rad/s. Every component halves when the physics rate doubles (ratios 1.98–2.00 at
1200 → 2400 Hz; to 9600 Hz in a scratch study), so the gap is PyBullet's first-order discretization of the ODE. Its
two parts: (i) after a command step, the simulator applies each substep's thrust at its end-of-substep value, about
`hPhys/2` ahead of the continuous thrust (predicted one-period `Δω` 7.9e-4 rad/s for a roll step, observed 7.83e-4; a
"substep model" with the thrust held per substep reduces it to 8.6e-8); (ii) PyBullet's own integration of the
rotation (tumble: `Δω` 4.8e-3 rad/s after 0.1 s, not reduced by the substep model; the Bullet mechanism was not
traced). No sign or frame error: the gaps are about 3% of the ODE's own change on each axis, and the frame conversion
round-trips to `1e-15`. Nothing was tuned.

**F8. The sharp command sensitivity.** With the lag, a command error reaches the rigid body only through the thrust,
which moves by `δ(1 - e^{-t/tauUp})` (0.18127 of a step after one period; `fmax` times that is 1.55 N per unit
command). The rates then move by `2 alphaMax δ lagM1(h) ≈ 0.0643 δ` rad/s, the velocity by `amax δ lagM1(h)
≈ 3.88e-3 δ` m/s, the position by `amax δ lagM2(h) ≈ 3.3e-6 δ` m (leading terms; the proved bounds with the
gyroscopic and tilt corrections are `0.0650`, `3.91e-3`, `3.48e-6`, `step_input_sens_num`). Without the lag the rates
would move by `2 alphaMax δ h ≈ 0.69 δ` rad/s: the lag cuts the one-period effect of a command error by a factor of
about 10. The thrust bound is attained for commands above the current thrust; a command below it acts through the
slower `tauDown` (a symmetric roll step from hover reaches 0.757 of the rate bound).

**F9. The clip in the force map.** The thrust state enters the force and torque maps clipped to `[0, 1]`. On the
physical range the clip is inactive (the range is invariant, `traj_thrustRange`), and it makes every force, torque
and energy bound hold on every state, which the truncation argument for global existence needs (a truncated curve is
only a scaled solution, whose thrust can leave `[0, 1]`; `f_scaledSol` bounds it by `(1 + |f|) e^{t/tauUp} - 1`).

**F10. Theorems that now need the thrust range.** The Euler comparison, the sharp translation and attitude steps, the
per-period deviations and the spin and level closed forms take `ThrustRange x` (thrusts in `[0, 1]⁴`) as a hypothesis:
the rate of the thrust is bounded by `1/tauUp` only there. The simulator's thrust is always in the range (`fmax` times
it), so the hypothesis holds on every state reachable from a simulator state.

**F11. The simulator's drone-model enum in `numcheck.py`.** gym-pybullet-drones requires a `drone_model` argument;
`sim/gorge_lockstep.py:188` passes the package's first enum member, whose only effect under `Physics.PYB` is the name
of the package URDF, which `AirframeAviary` replaces with the X500's. `numcheck.py` passes the same member as
`list(DroneModel)[0]` (asserting it is not `RACE`, whose yaw torques the package negates) so that the plant directory
names no other vehicle.
