# Findings

**F1. `sim/check_constants.py` does not check the plant constants.** `PLAN.md` (rule 6) and the task say it compares
`Constants.lean` with the simulator. It does not read any Lean plant file: it re-flies the Monte Carlo starts of
`sim/out/montecarlo` and checks the constants of the archived `contracts/Contracts/Mission/Sub.lean` (its docstring,
lines 1-17). No script in the repository reads the plant constants (`grep` for `Constants.lean`, `Contracts/Plant` over
`sim/`, `tests/`, `support/`). So `sim/check_constants.py` was not modified. A plant check was written instead:
`plant/tests/check_constants.py` (reads only; 0.02 s). Output:

```
OK   mass           Lean      0.027   simulator      0.027   (cf2x.urdf mass)
OK   Jx             Lean     1.4e-5   simulator     1.4e-5   (cf2x.urdf ixx)
OK   Jy             Lean     1.4e-5   simulator     1.4e-5   (cf2x.urdf iyy)
OK   Jz             Lean    2.17e-5   simulator    2.17e-5   (cf2x.urdf izz)
OK   armL           Lean     0.0397   simulator     0.0397   (cf2x.urdf arm)
OK   lever          Lean      0.028   simulator      0.028   (cf2x.urdf prop link inertial origins)
OK   kf             Lean   3.16e-10   simulator   3.16e-10   (cf2x.urdf kf)
OK   km             Lean   7.94e-12   simulator   7.94e-12   (cf2x.urdf km)
OK   thrust2weight  Lean       2.25   simulator       2.25   (cf2x.urdf thrust2weight)
OK   grav           Lean    9.80665   simulator    9.80665   (run_copter.py GRAVITY_MSS)
OK   h              Lean    1 / 400   simulator      1/400   (run_copter.py 1/CTRL_HZ)
INFO maxRPM = sqrt(thrust2weight g m / (4 kf)) = 21710.005924 rpm; fmax = kf maxRPM^2 = 0.148938 N; thrust2weight g m / 4 = 0.148938 N
all constants agree
```

**F2. Line numbers of `run_copter.py` had drifted.** The archive cited `run_copter.py:268, 271, 272, 331, 339-346,
383, 892`; on 2026-11-16 these definitions are at `272` (`env.G = GRAVITY_MSS`), `275` (`MAX_RPM`), `276`
(`MAX_THRUST`), `338` (`changeDynamics`, damping removed), `346-353` (`actuators_to_rpm`), `391` (`dt`), `900`
(`--pyb-hz`). They were corrected in the docstrings of `Plant/Model/Constants.lean` and `Field.lean` before the model
was frozen (`MODEL.sha256`); the definitions are unchanged. The `envs/BaseAviary.py` and `cf2x.urdf` citations were
checked and are correct.

**F3. CF2X ratios hard-coded as literals.** `gyro = 11/20` (`Field/Bounds.lean`, the bound `(Jz - Jx)/Jx` of the
gyroscopic coefficients) and the `31/20` (`= Jz/Jx`) in `Cd` (`Step/Sharp.lean`) are literals, not expressions in the
model constants. The audit's three rule-3 violations (`Cd_nonneg`, `Cd_mono`, `Katt_pos`) come from this: their
statements name only these functions. For the X500 the ratios are `11/13` and `24/13`, so `vf_sub_w`, `abs_vf_w`,
`abs_vf_wA`, `abs_dnDDot_le` and what depends on them would be false with X500 constants (`VEHICLES.md`, section 3).
Not changed (they are archive content, and `gyro`/`Cd` are outside the model).

**F4. The port needed no lemma renames.** The seven archive files built unchanged on Lean `v4.35.0` / Mathlib
`v4.35.0` with the module system (only the module and namespace names changed). One new theorem
(`sampledFlow_apply`, replacing the `rfl` inside `Mplant_const`) needed `change … ; rfl` instead of a term `rfl`,
because `Function.autonomousFlow` is not exposed by DynamicalSystems' module.

**F5. The joint sensitivity bound is loose away from the origin.** `norm_step_sub_step_le_exp` uses the Lipschitz
constant `K = Klip (box r)` of the whole field on the ball of radius `box r`, and `‖x‖` includes the position. Evaluated
with the CF2X constants (Python, not in Lean): `r = 1`: `box ≈ 5.0`, `K ≈ 896`, `e^{Kh} ≈ 9.4`, input factor
`Kin (e^{Kh} - 1)/K ≈ 11` per unit command (unit quaternion, `Kin = 2 alphaMax ≈ 1191`); `r = 2`: `e^{Kh} ≈ 27`, factor
`≈ 24`; `r = 5`: `e^{Kh} ≈ 1.3e3`; `r = 10`: `e^{Kh} ≈ 1.8e6`. The leading-order input sensitivity per period is
`Kin h ≈ 3`. The statements are correct but only useful near the origin (`OPEN.md`).

**F6. Numerical check of the phase-3 statements** (`plant/tests/numcheck.py`, RK4 at `h/400`, 0.4 s): on 40 random
states (unit quaternion, rates up to 10 rad/s) and commands in `[-0.2, 1.2]⁴`, 20 spin states and a 40-period level
flight: `unmix_wrench`, `norm_vf_sub_input_le`, `step_v_dev_le`, `step_p_dev_le`, `step_v_sub_le`, `vf_yawRot`,
`step_yawRot`, `step_spin` (closed form within 1e-10), `stepN_level_vz` and `stepN_level_pz` (within 1e-10) hold on every
sample; the input sensitivity was checked in the stronger form `≤ 1.6 Kin h ‖u - w‖` and held. No statement failed;
none of the phase-3 statements contains an evaluated number.
