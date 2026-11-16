# The Crazyflie plant as an ODE under zero-order hold

This package models the Crazyflie 2.x quadrotor as gym-pybullet-drones simulates it for
`cpp2lean/sim/run_copter.py`. The model is an ODE `ẋ = F(x, u)`. The four actuators are held
constant over each 400 Hz control period, so `F` is evaluated with a fixed `u` for the whole
period. The exact flow over one period is a step function, and that step is lifted into the
contract library as a discrete-time component. This replaces the port's forward-Euler recurrence
(`delegate-port/Contracts/CopterPlant.lean`, `dynR`).

The package uses Lean `v4.36.0-rc2` and Mathlib `v4.36.0-rc2`. It also depends on
DynamicalSystems (`https://github.com/mcdoll/DynamicalSystems`), pinned at commit
`b40b48ffbdf510e279a954ac8bf50ae4f926c71e`. Every file is a module under the new module system.

## Build

```
cd cpp2lean/contracts
lake exe cache get        # Mathlib oleans
lake build                # Contracts, FloatModel: no warnings, no sorry
lake env lean AxiomCheck.lean   # axiom audit of the main theorems
```

## Files

| file | content |
|---|---|
| `Contracts/Basic.lean`, `STL.lean`, `Lift.lean` | the port's generic contract library (contracts, STL, `liftStatic`/`liftDyn`/`liftHidden`/`liftStep`, `langOn`, `initOn`). The content is unchanged; each file was turned into a module (`module`, `public import`, `@[expose] public section`), and one deprecated import name was updated. |
| `FloatModel/ToReal.lean` | the port's exact real semantics of floats, generic over formats, plus the binary64 reading `Float.toReal`/`Float.IsFinite`. Fixed for v4.36: `Format.he` is now `2 ≤ exponentBits`, and `if_pos`/`if_neg`/`dif_neg` were renamed to `ite_eq_left`/`ite_eq_right`/`dite_eq_right`. |
| `FloatModel/Float32.lean` | the binary32 reading `Float32.toReal`/`Float32.IsFinite` (the definitional part of the port's `Float32.lean`, which the sensing ports need). The rounding bounds are not carried over. |
| `Contracts/Plant/Constants.lean` | constants with their sources, `kf_maxRPM_sq` |
| `Contracts/Plant/Field.lean` | frames, motor slots, the named state `State`, the flat state `X`, and the vector field `vf` |
| `Contracts/Plant/Bounds.lean` | explicit force and torque bounds, block-wise Lipschitz bounds, the ball constants `Klip`/`Mbd` |
| `Contracts/Plant/Invariants.lean` | `‖q‖²` invariance, the energy estimate, and the one-period box `box` for scaled solutions |
| `Contracts/Plant/Flow.lean` | the truncated field and its flow, `traj`, `step`, uniqueness, the Grönwall bound, hover |
| `Contracts/Plant/Euler.lean` | `step` against `eulerStep`, the specific force against the backward difference, and the relation to the port's Euler-angle plant |
| `Contracts/Plant/Sharp.lean` | the sharp one-period step, block by block: exact integration of the `p` and `v` rows, Grönwall on the attitude block alone, evaluated constants |
| `Contracts/Plant/Quadrotor.lean` | the sample, the sensing ports, the plant state, the lift `Mplant`, the sampled flow, hover of the plant |
| `AxiomCheck.lean` | `#print axioms` of the main theorems (not part of the library) |

## Equations

The state is `x = (p, v, q, ω) ∈ X = Fin 13 → ℝ`, with the sup norm. The blocks are:

* `p`: position, NED, coordinates 0–2;
* `v`: velocity, NED, coordinates 3–5;
* `q = (q1, q2, q3, q4)`: attitude quaternion, body (FRD) to NED, `q1` the scalar part (ArduPilot's
  order), coordinates 6–9;
* `ω = (p, q, r)`: body rates, FRD, coordinates 10–12.

`State` is the named view of the same data. `State.toX` and `State.ofX` convert between the two;
they are mutually inverse (`ofX_toX`, `toX_ofX`).

For held actuators `u` (clipped to `[0,1]` inside the field, `clip01`):

```
fᵢ  = fmax · clip01(uᵢ)                         motor force along body up
T   = f₀ + f₁ + f₂ + f₃                          accel u = T / m ∈ [0, amax]
τx  = a (-f₀ + f₁ + f₂ - f₃)                     a = lever = 0.028
τy  = a ( f₀ - f₁ + f₂ - f₃)
τz  = km MAX_RPM² (u₀ + u₁ - u₂ - u₃) = (km/kf) fmax (u₀ + u₁ - u₂ - u₃)

ṗ = v
v̇ = g e_z - (T/m) d(q),     d(q) = q ⊗ (0, e_z) ⊗ q̄
       = (2(q2 q4 + q1 q3), 2(q3 q4 - q1 q2), q1² - q2² - q3² + q4²)
q̇ = ½ q ⊗ (0, ω)
ω̇ = J⁻¹ (τ - ω × J ω),      J = diag(Jx, Jy, Jz)
```

`d(q)` is `‖q‖²` times the body down axis of the rotation `q/‖q‖`. For a unit quaternion it is the
third column of `R(q)`. Since `‖q‖` is invariant (proved below), the two forms agree along every
solution that starts on the unit sphere. The specific force is `specForce q u = -(T/m) d(q)`.

The step is `step x u = Φ_u(h, x)`, the state after one period `h = 1/400` s of `ẋ = F(x, u)`.
`eulerStep x u = x + h F(x, u)` is the forward-Euler step of the same field.

## Constants

Simulator paths are relative to `sim/.venv/lib/python3.12/site-packages/gym_pybullet_drones/`.
The driver is `cpp2lean/sim/run_copter.py`. Its line numbers refer to the version of
2026-11-05 13:06, which is still being edited, so the numbers may drift. The definitions they
point to are named alongside.

| Lean name | value | source |
|---|---|---|
| `mass` | 0.027 kg | `assets/cf2x.urdf:11` |
| `Jx`, `Jy`, `Jz` | 1.4e-5, 1.4e-5, 2.17e-5 kg m² (products 0) | `assets/cf2x.urdf:12`, loaded with `URDF_USE_INERTIA_FROM_FILE` (`envs/BaseAviary.py:488`); the prop links have mass and inertia 0 (`cf2x.urdf:43-44, 55-56, 67-68, 79-80`) |
| `armL` | 0.0397 m | `assets/cf2x.urdf:5` (`arm`); used only by `_dynamics` as `L/√2` (`envs/BaseAviary.py:847-848`) |
| `lever` | 0.028 m | motor link origins `(±0.028, ±0.028, 0)`, `assets/cf2x.urdf:42, 54, 66, 78`; the lever of `Physics.PYB` (`_physics`, `envs/BaseAviary.py:690-699`) |
| `kf` | 3.16e-10 N/rpm² | `assets/cf2x.urdf:5` |
| `km` | 7.94e-12 N m/rpm² | `assets/cf2x.urdf:5` |
| `thrust2weight` | 2.25 | `assets/cf2x.urdf:5` |
| `grav` | 9.80665 m/s² | `GRAVITY_MSS`, `run_copter.py:89`, written over the environment's `9.8` (`envs/BaseAviary.py:74`) in `make_env` (`run_copter.py:268`) |
| `maxRPM` | `√(2.25 · g · m / (4 kf))` = 21710.006 rpm | `run_copter.py:271` (formula of `envs/BaseAviary.py:119`) |
| `fmax` | `kf · MAX_RPM²` = 0.148938 N | a quarter of `MAX_THRUST`, `run_copter.py:272` |
| `h` | 1/400 s | `CTRL_HZ = 400`, `run_copter.py:86`; `dt = 1.0 / CTRL_HZ`, `run_copter.py:383` |
| `amax` | `thrust2weight · g` = 22.06496 m/s² | derived: `4 fmax / m` (`four_fmax_div_mass`) |
| `kmkf` | `km/kf` = 0.025127 m | derived |
| `alphaMax` | `2 · lever · fmax / Jx` = 595.754 rad/s² | derived bound on `|τᵢ/Jᵢ|` (the yaw axis gives 344.914) |
| `dtUs` | 2500 µs | the period field of the sample |

Proved identities:

* `kf_maxRPM_sq : kf * maxRPM ^ 2 = thrust2weight * grav * mass / 4`
* `four_kf_maxRPM_sq : 4 * kf * maxRPM ^ 2 = thrust2weight * mass * grav`

The hover thrust fraction is therefore `1/thrust2weight` (`accel_hover`).

## Frames and motor slots

ArduPilot's frames are used throughout: NED world, FRD body. `run_copter.py` converts each
simulator observation (ENU world, FLU body) with fixed proper rotations:

* `T = ENU_TO_NED = [[0,1,0],[1,0,0],[0,0,-1]]` (`run_copter.py:40`);
* `D = FRD_TO_FLU = diag(1,-1,-1)` (`run_copter.py:45`).

Then (`enu_state_to_ned`, `run_copter.py:66-75`):

* `p_ned = T p_enu`, `v_ned = T v_enu`;
* `R_ned_frd = T R_enu_flu D`;
* `ω_frd = R_ned_frdᵀ T ω_world` (PyBullet reports the world-frame angular velocity).

The quaternion is `q_ned_frd = q(T) ⊗ q_pyb ⊗ q(D)`, with `q(T) = (0, √½, √½, 0)` and
`q(D) = (0, 1, 0, 0)`. It is normalized, and its sign is chosen so that `q1 ≥ 0` (`quat_ned_frd`,
`run_copter.py:118-126`).

The motor slot map is `SLOT_TO_SIM = [0, 2, 3, 1]` (`run_copter.py:92-98`):

| slot | position | spin | sim prop | FLU link position | yaw torque sign (FRD z) |
|---|---|---|---|---|---|
| 0 | front right | CCW | 0 | `(+a, -a)` | `+` |
| 1 | rear left | CCW | 2 | `(-a, +a)` | `+` |
| 2 | front left | CW | 3 | `(+a, +a)` | `-` |
| 3 | rear right | CW | 1 | `(-a, -a)` | `-` |

A force `f` along FLU `+z` applied at FLU `(rx, ry, 0)` has the moment `(ry f, -rx f, 0)`.
Summing over the slots and converting to FRD gives the `τx` and `τy` above. The yaw torque is
`(-t0 + t1 - t2 + t3)` over sim props in FLU (`envs/BaseAviary.py:694`), which is `τz` above
after the slot map and the FLU-to-FRD flip.

Cross-check against `_dynamics` (`envs/BaseAviary.py:844-848`, `CF2X`). It computes
`x_torque = -(F0+F1-F2-F3) L/√2` and `y_torque = (-F0+F1+F2-F3) L/√2` over sim props. In slots
these are `a(-f₀+f₁+f₂-f₃)` (FRD `τx`) and `a(-f₀+f₁-f₂+f₃)` (FRD `-τy`), so the signs agree.

## What is proved

All statements are about `vf`, `traj`, `step` and `eulerStep` as defined above. `u` is arbitrary
(it is clipped inside the field).

**Lipschitz and bounds**

* `vf_lipschitz_ball`: `‖x‖ ≤ R → ‖y‖ ≤ R → ‖vf x u - vf y u‖ ≤ Klip R * ‖x - y‖`, with
  `Klip R = 1 + (8 amax + 3) R`.
* `vf_locallyLipschitz`: `LocallyLipschitz (fun x => vf x u)`.
* `norm_vf_le`: `‖x‖ ≤ R → ‖vf x u‖ ≤ Mbd R`, with `Mbd R = R + g + alphaMax + (4 amax + 2) R²`.
* Block versions: `vf_sub_p`, `vf_sub_v`, `vf_sub_q`, `vf_sub_w`, `abs_vf_v`, `abs_vf_q`,
  `abs_vf_w`.

**Global flow by truncation** (`Flow.lean`)

* `vfT R u = vf (radialTrunc R ·) u` is globally Lipschitz with constant `2 Klip R`
  (`vfT_lipschitz`).
* `flowT R u` is its flow, from `LipschitzWith.exists_autonomousFlow`. That library theorem is
  proved: it rests on `global_existence`, Mathlib's Picard–Lindelöf and uniqueness, and
  `lipschitzWith_radialTrunc`, all with standard axioms. None of the library's `proof_wanted`
  statements is used (`UniformlyLocallyLipschitz.isCompleteVectorField`,
  `IsFundamentalSolution.continuous`, `exists_nonAutonomousFlow`, …).
* The truncation is a scaling `c • y` with `c ∈ [0,1]` (`radialTrunc_eq_smul`). So a curve of
  `flowT` is a *scaled solution* (`scaledSol_flowT`), and the a priori estimates below apply to it.

**A priori estimates for scaled solutions** (`Invariants.lean`)

* `qnormSq_scaledSol`: `‖q‖²` is constant. The identity is `Σ qᵢ (q ⊗ (0,ω))ᵢ = 0`
  (`q_dot_scaled`).
* `energy_scaledSol`: with `E = ωᵀJω`, `E(t) + cτ h² ≤ (E(0) + cτ h²) e^{t/h}`. This holds because
  `Ė = 2 ω·τ` (the gyroscopic term does no work, `energy_dot_scaled`) and `2 ω·τ ≤ E/h + h cτ`.
* `v_scaledSol`, `p_scaledSol`: velocity and position grow at most linearly.
* `norm_le_box_of_scaledSol`: over `[0,h]` from `‖γ 0‖ ≤ r`, `‖γ t‖ ≤ box r`, where
  `box r = max(pB r, vB r, qB r, wB r)`:
  * `vB r = r + h(g + 4 amax r²)`,
  * `pB r = r + h vB r`,
  * `qB r = 2r`,
  * `wB r = √(((Jx+Jy+Jz) r² + cτ h²) e / Jx)`.

**The step** (`Flow.lean`). `traj x u t = flowT (box ‖x‖) u t x` and `step x u = traj x u h`.

* `traj_hasDerivAt`: `∀ t ∈ Icc 0 h, HasDerivAt (traj x u) (vf (traj x u t) u) t`. The truncation
  is never active along the trajectory. `traj_isIntegralCurveOn` is the same fact stated as
  `IsIntegralCurveOn`.
* `step_spec`: `∃ γ, γ 0 = x ∧ γ h = step x u ∧ ∀ t ∈ Icc 0 h, HasDerivAt γ (vf (γ t) u) t`.
* `traj_unique` / `step_unique`: a curve `γ` that is continuous on `[0,h]`, has `γ 0 = x`, and has
  right derivative `vf (γ t) u` on `[0,h)` satisfies `EqOn γ (traj x u) (Icc 0 h)` and
  `γ h = step x u`. Uniqueness needs no a priori assumption: both curves lie in a common ball, and
  `F` is Lipschitz there.
* `step_eq_flowT`: `box ‖x‖ ≤ R → flowT R u h x = step x u`. The step does not depend on the
  truncation radius.
* `qnormSq_const_of_solution`, `qnormSq_traj`, `qnormSq_step`: `‖q‖²` is constant along every
  solution, so the unit sphere is invariant.
* `norm_traj_sub_le`:
  `∀ t ∈ Icc 0 h, ‖traj x u t - x‖ ≤ gronwallBound 0 (Klip (box ‖x‖)) ‖vf x u‖ t`.
  The explicit form `‖F(x,u)‖ (e^{Kt} - 1)/K` is `norm_traj_sub_le_exp`. The version on a ball is
  `norm_traj_sub_le_ball`: `‖x‖ ≤ r →` the same bound with `K = Klip (box r)`. The linear version
  is `norm_traj_sub_le_mul`: `Mbd (box ‖x‖) · t`.
* `vf_hover`: `(∀ i, u i = 1/thrust2weight) → vf (hoverX z) u = 0`.
* `step_hover`: under the same hypothesis, `step (hoverX z) u = hoverX z`.

**Euler comparison** (`Euler.lean`)

* `step_sub_eulerStep_le`:
  `qnormSq x ≤ Q → WBd x W → ‖step x u - eulerStep x u‖ ≤ eulerC Q W * h ^ 2`.
  Here `WBd x W` means all body rates are at most `W` in absolute value. The constant is
  `eulerC Q W = cE Q W / 2`, and `cE` is the largest of four block constants:
  * `p` rows: `Mv = g + amax Q`;
  * `v` rows: `cV = 8 amax √Q Mq`;
  * `q` rows: `(3/2)(√Q Mw + wT W · Mq)`;
  * `ω` rows: `2 gyro (wT W) Mw`.

  These use the trajectory bounds `wT W = W + h(alphaMax + gyro (wB W)²)`,
  `Mq = (3/2)√Q wT W`, `Mw = alphaMax + gyro (wT W)²`, and `gyro = 11/20`.
* `step_sub_eulerStep_le_ball`: `‖x‖ ≤ r → ‖step x u - eulerStep x u‖ ≤ eulerC (4r²) r * h²`.

Values for a unit quaternion (`Q = 1`), sup norm, per step:

| `W` (rad/s) | `wT W` | `eulerC · h²` | `cV · h/2` (m/s²) |
|---|---|---|---|
| 0 | 1.51 | 3.10e-3 | 0.50 |
| 1 | 2.52 | 5.20e-3 | 0.84 |
| 2 | 3.56 | 7.38e-3 | 1.18 |
| 5 | 6.84 | 1.46e-2 | 2.27 |
| 10 | 12.84 | 3.03e-2 | 4.25 |

The `ω` block dominates `eulerC`. Bounds per block are in the proof (`vf_traj_sub`). For example,
at `W = 1` the `v` rows are within 2.1e-3 m/s per step and the `p` rows within 1.0e-4 m.

* `downAxis_quatOf`: `downAxis (quatOf roll pitch yaw) = thrustDir roll pitch yaw`. Also
  `normSq_quatOf`: the quaternion of Euler angles is a unit quaternion.
* `eulerStep_pv_quatOf`: at a state whose attitude is `quatOf roll pitch yaw`, the `p` and `v`
  rows of `eulerStep` are exactly the rows of the port's `dynR`: `p + h v` and
  `v + h(g e_z - (T/m) thrustDir)`, with the same `g`, `h` and thrust law. The other rows differ:
  * the `ω` rows differ only in the lever arm: 0.028 here, `armL/√2 = 0.028072` in `dynR`;
  * the attitude rows are Euler steps of different kinematics (quaternion here, ZYX angles in
    `dynR`).

  So `dynR` results transfer to `step` in two parts. The `p` and `v` rows transfer with the margin
  `eulerC · h²`. The attitude row additionally needs the Euler-angle vs quaternion step gap, which
  is not formalized.

**The sharp one-period step** (`Sharp.lean`)

The bounds above are too coarse per tick: `norm_traj_sub_le` puts the position into the Lipschitz
radius, and the `v` rows of `step_sub_eulerStep_le` go through a Lipschitz bound of the down axis
(`cV · h/2 = 0.84` m/s² at `W = 1`). `Sharp.lean` treats the blocks separately. Hypotheses, as in
`Euler.lean`: `qnormSq x = 1`, `WBd x W` (each body rate at most `W`), and a torque bound
`TorqueBd u A` (`|τx/Jx|, |τy/Jy|, |τz/Jz| ≤ A`). Every `u` satisfies `TorqueBd u alphaMax`
(`torqueBd_alphaMax`). Actuators in `[lo, lo + s] ⊆ [0, 1]` give `TorqueBd u (alphaMax · s)`
(`torqueBd_of_spread`), and actuators at most `c` give `accel u ≤ c · amax` (`accel_le_mul`).

Notation (all in `Sharp.lean`):

* `pI j`, `vI j` (`j : Fin 3`), `qI i`, `wI k`: the coordinates of `p`, `v`, `q`, `ω`; `ez = (0, 0, 1)`;
* `dn x j`: the down axis `d(q)` (the components of `downAxis`, `dn_eq_downAxis`); `col0`, `col1`:
  the first two columns of the rotation, times `‖q‖²`;
* `dnDot x j = col0 x j · ω_y - col1 x j · ω_x`: the exact `Dd(q)[q̇] = R(q)(ω × e_z)`;
* `dnDDot x u j = col0 (ω̇_y + ω_x ω_z) + col1 (ω_y ω_z - ω̇_x) - dn (ω_x² + ω_y²)`: the second
  derivative of `d` along the flow (`hasDerivAt_dn`, `hasDerivAt_dnDot`);
* `wTA W A = W + h (A + gyro (wB W)²)`: the rate bound over the period (`WBd_trajA`);
* `Cd A Ω = √(2 (A + (31/20) Ω²)² + 4 Ω⁴)`, with `31/20 = Jz/Jx`: `|dnDDot| ≤ Cd A Ω` for a unit
  quaternion (`abs_dnDDot_le`; the rotation rows have unit length, `row_sq`, `abs_row_le`); also
  `|dnDot| ≤ √2 Ω` (`abs_dnDot_le`);
* `att x : Fin 7 → ℝ`: the attitude block `(q, ω)`, sup norm; `Katt Ω = max((3/2)(1 + Ω), 2 gyro Ω)`;
  `attF0 W A = max((3/2) W, A + gyro W²)`.

Statements, for `Ω ≥ wTA W A` and `a = accel u` (the thrust acceleration, constant over the
period):

* `step_pv_sharp`: for each NED component `j`,
  ```
  |step x u (vI j) - (x (vI j) + h (g ez j - a dn x j) - a (h²/2) dnDot x j)| ≤ a Cd A Ω h³/6
  |step x u (pI j) - (x (pI j) + h x (vI j) + (h²/2)(g ez j - a dn x j) - a (h³/6) dnDot x j)|
      ≤ a Cd A Ω h⁴/24
  ```
  `traj_pv_sharp` is the same for every `t ∈ [0, h]` along the trajectory. The proof integrates
  `v̇ = g e_z - a d(q(t))` and `ṗ = v` exactly (`taylor2`, `taylor3`, `taylor4`, from
  `image_norm_le_of_norm_deriv_right_le_deriv_boundary`). Only `d̈` is bounded.
* `traj_pv_first`: one order less, `|v(t) - v - t(g e_z - a d)| ≤ a √2 Ω t²/2` and
  `|p(t) - p - t v - (t²/2)(g e_z - a d)| ≤ a √2 Ω t³/6`.
* `traj_pos_move`, `step_pos_move` (intersample): with `VBd x V`, on `[0, h]`,
  `|v_j(t) - v_j| ≤ (g + a) t` and `|p_j(t) - p_j| ≤ V t + (g + a) t²/2`.
* `vf_att_lipschitz`: `QBd x 1 → WBd x Ω → WBd y Ω →
  ‖att (vf x u) - att (vf y u)‖ ≤ Katt Ω · ‖att x - att y‖`. No position or velocity enters.
* `traj_qw_gronwall`: `‖att (traj x u t) - att x‖ ≤ gronwallBound 0 (Katt Ω) ‖att (vf x u)‖ t` on
  `[0, h]` (Grönwall on the attitude block only), and `step_qw_gronwall`:
  `‖att (step x u) - att x‖ ≤ attF0 W A / Katt Ω · (e^{Katt Ω · h} - 1)`.
* `traj_att_taylor`: on `[0, h]`, `|q_i(t) - q_i| ≤ Mq1 Ω t`, `|q_i(t) - q_i - t q̇_i| ≤ cQ A Ω t²/2`,
  `|ω_k(t) - ω_k| ≤ Mw1 A Ω t`, `|ω_k(t) - ω_k - t ω̇_k| ≤ cW A Ω t²/2`, with `Mq1 Ω = (3/2) Ω`,
  `Mw1 A Ω = A + gyro Ω²`, `cQ = (3/2)(Mw1 + Ω Mq1)`, `cW = 2 gyro Ω Mw1`.
* `qnormSq_step` (unchanged) keeps the unit sphere.

Evaluated constants (theorems and `example`s at the end of `Sharp.lean`, checked by `norm_num`
with `Real.exp_one_lt_d9` for the energy box):

| case | `A` (rad/s²) | `Ω` | `Cd` | bound on `r_v` (m/s) | bound on `r_p` (m) |
|---|---|---|---|---|---|
| `W = 1`, any actuators (`a ≤ amax`) | `alphaMax ≤ 595.76` | `2.53` (`wTA_one_alphaMax_le`) | `≤ 857` (`Cd_alphaMax_le`) | `≤ 4.93e-5` | `≤ 3.1e-8` |
| `W = 1`, any torque, hover thrust (`a = g`) | `alphaMax` | `2.53` | `≤ 857` | `≤ 2.19e-5` | |
| `W = 1`, actuators in `[0.30, 0.62]` (`a ≤ 0.62 amax`) | `0.32 alphaMax ≤ 190.65` | `1.52` (`wTA_one_spread_le`) | `≤ 275` (`Cd_spread_le`) | `≤ 9.8e-6` | |

As an acceleration, `|r_v| / h ≤ 0.0197` m/s² in the first row, against `0.84` m/s² for
`cV · h/2`. Other values at `W = 1`, any actuators, `Ω = 2.53`:

* the attitude Lipschitz constant is `Katt = 5.295`;
* the attitude block moves by at most `1.511` per period (`step_qw_gronwall`). The rates dominate:
  under full torque they change by up to `h · alphaMax = 1.49` rad/s per period;
* the attitude remainders are `cQ h²/2 ≤ 2.86e-3` and `cW h²/2 ≤ 5.22e-3` rad/s;
* the intersample position move at `|v_j| ≤ 1.5` m/s is at most `1.5 h + (g + amax) h²/2 ≤ 3.85e-3` m.

**Specific force**

* `backwardDiff_sub_specForce`: `qnormSq x ≤ Q → WBd x W →` for the three NED components,
  `|(v(h) - v(0))/h - g e_z - specForce(step x u)| ≤ cV Q W * h / 2`. The left side compares the
  backward difference of the exact velocity minus gravity, which is the quantity the driver
  computes, with the model's instantaneous value at the tick.

**The sampled plant** (`Quadrotor.lean`)

* `Mplant sense32 senseP = liftStep (·.phys) (·.act) (·.smp) (plant sense32 senseP)` over the
  universe `CX`. `CX` has the fields `phys : PState`, `smp : Sample` and
  `act : Vector Float32 4`, as in the port's `CopterPlant.CX`.
* `PState` has two fields: the rigid-body state `x`, and `held`, the thrust fractions of the
  period that ended at the tick.
* `next s a = ⟨step s.x (act a), act a⟩`.
* `sample` reads the state only: `pos` through `senseP`; `vel`, `accel_ef`, `quat` and `gyro`
  through `sense32`; and `dt_us = 2500`.
* `mem_Mplant` unfolds membership in the component.
* `Mplant_flow`: every tick of a plant behavior is the endpoint of an ODE solution over the
  period, with the previous tick's actuators held.
* `Mplant_qnormSq`: `‖q‖²` is the same at every tick of a behavior.
* `Mplant_const`: under constant actuators the state at tick `n` is `sampledFlow u n x₀`, where
  `sampledFlow u = Function.autonomousFlow (step · u)` is the library's discrete flow.
* `nextR_hover`, `tickSpecForce_hover`, `sample_hover` describe hover. The hover sample is
  `pos (0,0,senseP z)`, `vel 0`, `accel_ef (0,0,sense32 (-g))`, `quat (1,0,0,0)`, `gyro 0`.

## What is assumed

* **Sensing ports.** The ports are hypotheses, not definitions (`Sense32Spec`, `SensePSpec`,
  `CopterSense`), with the same structure as in the port. On `|r| ≤ R` each reading is finite and
  within `ε|r| + η`. Both ports send `0` to `+0`, and the `float` port sends `1` to `1`. Round to
  nearest gives `(2⁻²⁴, 2⁻¹⁵⁰)` on `|r| ≤ 100` and `(2⁻⁵³, 2⁻¹⁰⁷⁵)` on `|r| ≤ 10⁴`. They are
  stated with the exact readings `Float32.toReal`/`Float.toReal` of Lean's bit-level float model.
* **The rigid body.** The model assumes the physics the simulator is configured for:
  * a single rigid body with the URDF inertia;
  * motor forces along body up at the motor links;
  * the drag torques of `_physics`;
  * gravity `GRAVITY_MSS`;
  * no damping;
  * Euler's equations for the rotation, including the gyroscopic term `ω × Jω`, which PyBullet's
    multibody dynamics also includes.

  The lever arm `0.028` follows from `_physics` applying each force at its prop link's inertial
  origin. The prop links are attached by fixed joints with zero joint origin, so a force at the
  URDF link frame would give no roll or pitch torque. The simulated vehicle does roll and pitch,
  so the forces act at the inertial origins.
* No other hypotheses. There are no axioms beyond `propext`, `Classical.choice`, `Quot.sound`.

## Where the model differs from the simulator

1. **Integration scheme.** The model is the exact flow over `h`. PyBullet integrates the rigid
   body with its own semi-implicit scheme: `PYB_STEPS_PER_CTRL = 3` substeps of 1/1200 s per tick,
   with the motor speeds held over the three substeps, which is the same zero-order hold. The
   simulated state therefore differs from `step` by PyBullet's integration error (first order in
   1/1200 s per tick). This difference is not bounded in Lean, because PyBullet's integrator is not
   modeled.
2. **Quaternion normalization.** PyBullet renormalizes the base orientation after each substep.
   The model has no normalization term. Instead, `‖q‖` is invariant under the exact flow
   (`qnormSq_step`), so a unit initial quaternion stays a unit quaternion.
3. **Reported quaternion sign.** The driver normalizes the reported quaternion and flips its sign
   so that `q1 ≥ 0` (`quat_ned_frd`). The model reports the continuous `q` of the flow, which
   represents the same rotation but can have `q1 < 0` after rotations beyond a half turn about any
   axis.
4. **Specific force.** The driver reports `(v_k - v_{k-1})/h - g e_z` from the simulated
   velocities (`SpecificForce.update`, `run_copter.py:144-162`). The model reports the
   instantaneous `-(T/m) d(q)` at the tick, with the thrust held over the last period. For the
   exact flow the two differ by at most `cV Q W · h/2` per component (`backwardDiff_sub_specForce`;
   the table above gives values). On top of that comes the simulator's integration error. Before
   the first tick the driver reports `(0,0,-g)` on the ground or `0` in the air. The model reports
   the specific force of whatever `held` the initial plant state carries.
5. **Ground contact.** The driver starts the vehicle on the ground plane and lets it settle on the
   contact (`reset_env`). The model has no ground. It describes the vehicle in the air only.
6. **Lever arm vs the explicit model.** The lever `0.028` matches `Physics.PYB`. The simulator's
   alternative `_dynamics` (`Physics.DYN`, not used by the driver) and the port's Euler plant use
   `armL/√2 = 0.028072`, which is 0.26 % longer.
7. **Left out**, as in `Physics.PYB` and the port: drag, ground effect, downwash, motor and
   propeller dynamics (the thrust follows the actuator within the tick), battery, air density, and
   sensor noise, bias and delay beyond the rounding of the ports.

## Axiom audit (`lake env lean AxiomCheck.lean`)

```
'Contracts.Plant.kf_maxRPM_sq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Plant.vf_lipschitz_ball' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Plant.vf_locallyLipschitz' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Plant.norm_vf_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Plant.vfT_lipschitz' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Plant.norm_le_box_of_scaledSol' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Plant.traj_hasDerivAt' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Plant.step_spec' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Plant.traj_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Plant.step_unique' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Plant.step_eq_flowT' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Plant.qnormSq_const_of_solution' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Plant.qnormSq_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Plant.norm_traj_sub_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Plant.norm_traj_sub_le_ball' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Plant.norm_traj_sub_le_exp' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Plant.step_sub_eulerStep_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Plant.step_sub_eulerStep_le_ball' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Plant.backwardDiff_sub_specForce' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Plant.downAxis_quatOf' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Plant.eulerStep_pv_quatOf' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Plant.vf_hover' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Plant.step_hover' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Plant.nextR_hover' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Plant.sample_hover' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Plant.Mplant_flow' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Plant.Mplant_qnormSq' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Plant.Mplant_const' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Plant.torqueBd_alphaMax' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Plant.torqueBd_of_spread' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Plant.accel_le_mul' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Plant.WBd_trajA' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Plant.hasDerivAt_dn' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Plant.hasDerivAt_dnDot' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Plant.abs_dnDot_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Plant.abs_dnDDot_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Plant.traj_dn' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Plant.traj_pv_sharp' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Plant.step_pv_sharp' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Plant.traj_pv_first' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Plant.traj_pos_move' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Plant.step_pos_move' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Plant.vf_att_lipschitz' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Plant.norm_att_vf_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Plant.traj_qw_gronwall' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Plant.step_qw_gronwall' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Plant.traj_att_taylor' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Plant.wTA_one_alphaMax_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Plant.Cd_alphaMax_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Plant.wTA_one_spread_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'Contracts.Plant.Cd_spread_le' depends on axioms: [propext, Classical.choice, Quot.sound]
```

## Notes on the library

* Two library bodies are opened with `import all`: `radialTrunc` (in `Flow.lean`, to show that the
  truncation is a scaling) and `Function.autonomousFlow` (in `Quadrotor.lean`, an iterate).
* The library's global existence for locally Lipschitz fields,
  `UniformlyLocallyLipschitz.isCompleteVectorField`, is a `proof_wanted`, so it is not used. Its
  commented-out `IsCompleteVectorField.flow` is not used either. Completeness over one period is
  obtained here from the a priori estimates instead, and they hold for every initial state.
