# The vertical channel of the ArduCopter port at a hover sample

Phase 7c of the ArduCopter-to-Lean port (branch
`port`). This note derives the exact vertical closed loop at 400 Hz. It covers the ported
controller (`AC_PosControl.D_update_controller` → `AC_AttitudeControl_Multi.set_throttle_out` →
`AP_MotorsMulticopter.output`) and the Crazyflie plant of `Contracts/CopterPlant.lean`. It then
gives the analysis the vertical half of the hover proof needs: the eigenvalues, a rational
Lyapunov function, the contraction factor, the sublevel set inside the hover box, and the
perturbation slack compared with the binary32 rounding budget. The Lean side is
`Contracts/CopterVert.lean` (definitions and proofs) and `Contracts/CopterPlant.lean` (the plant).

All scripts that produced the numbers below are in the session scratchpad
(`.../scratchpad/vert/`: `model.py`, `reduce.py`, `lyap.py`, `ratP.py`, `cert.py`, `budget.py`,
`final.py`, `closedloop.py`, `compare.py`, `gen.py`). They use exact `fractions.Fraction`
arithmetic for every certified number, `numpy`/`scipy` only to search for the Lyapunov function,
and `sympy` for an exact inverse.

## 1. Configuration

- ArduPilot 802db19de1 as ported. Main loop 400 Hz, `FSTRATE_ENABLE = 0`.
- Parameters: `sim/params/copter-cf2x.txt` followed by `sim/params/copter-hover.txt`. That gives
  the linear thrust configuration `MOT_THST_EXPO 0`, `MOT_SPIN_MIN 0`, `MOT_SPIN_MAX 1`, plus
  `MOT_BAT_VOLT_MAX 0` and `MOT_HOVER_LEARN 0`. It sets `MOT_THST_HOVER 0.4444` and the single
  waypoint `(0, 0, -1)`. Every `PSC_D_*` gain keeps its code default (`AC_PosControl.cpp:51-80`,
  `:360-361`). `run.air_density_ratio = 1`.
- Plant: the CF2X with thrust-to-weight `2.25`, so vertical acceleration (down) is
  `g - 2.25 g u = g (1 - u/hover)` with `hover = 1/2.25 = 4/9`. Gravity is `g = 9.80665`, the
  value `sim/run_copter.py` gives the simulator. Period `h = 1/400` exactly.
- Hover sample: level attitude, horizontal position, velocity and targets zero, yaw target zero.
  The zero-half lemmas (other agents) establish that the horizontal and rotational channels are
  then exactly zero. The vertical path below relies on the following consequences of that, which
  those lemmas must deliver:
  - `rpy` inputs `±0`, so the matrix mixer passes the throttle through exactly;
  - `get_throttle_boosted` multiplies by exactly `1`, which needs `cos_tilt = 1`,
    `inverted_factor = 1` and `cos(_thrust_angle_rad) = cos 0 = 1`, the last one a libm
    hypothesis;
  - `get_compensation_gain = 1 * (1/1) = 1`;
  - `thrust_to_actuator(t) = 0 + 1 * (1 * t * 1) = t`, and the slew limit is `constrain(t, 0, 1)`.

  Hence the actuator equals the throttle filter output, bit for bit.
- The navigator target is fixed at `z = -1` with zero velocity and acceleration feed-forward. See
  section 11 for a caveat.

## 2. Tick order and the one-tick delay (`Copter/Loop.lean`)

Tick `t` reads the sample of plant state `x_t`. It then runs, in this order:

1. `motors_output_main`, which filters the `_throttle_in` that `set_throttle_out` stored at tick
   `t-1`:
   `F_t = F_{t-1} + (T_{t-1} - F_{t-1}) α_m`.
   The actuator is `u_t = F_t`. It drives the plant over `[t, t+1]`.
2. `read_AHRS`, `read_inertia`: the sample of `x_t`. Its specific force is the backward
   difference of velocity over `[t-1, t]` minus `g e_z` (`run_copter.py`, and `CState.sf` in
   `CopterPlant`). It therefore reflects `u_{t-1}`: `f_t = -2.25 g u_{t-1}` (vertical, level).
3. `ModeAuto.run` → `D_update_controller` → `set_throttle_out(T_t)`.

So the throttle computed at tick `t` reaches the plant over `[t+1, t+2]`. The accelerometer at
tick `t` sees the actuator of tick `t-1`. Both delays come from the call order; nothing in the
code models them.

## 3. The vertical path, operation by operation (`Float32` unless stated)

Notation: `z` is the NED position (target `z* = -1`), `w` the NED vertical velocity, `f` the
vertical specific force. `fl(·)` is one rounding. Model: `|fl(x) - x| ≤ 2⁻²⁴|x| + 2⁻¹⁵⁰`, and for
binary64 `2⁻⁵³|x| + 2⁻¹⁰⁷⁵`.

Sensing (plant ports, `CopterSense`):
- s1. `z_s = senseP(z)` (binary64).
- s2. `w_s = sense32(w)`.
- s3. `f_s = sense32(f)`, with `f ≈ -9.80665`.

`AC_P_1D.update_all` (`PSC_D_POS_P = 1`):
- o1. `fl64(z* - z_s)`.
- o2. `tofloat` (narrowing to binary32).
- o3. `sqrt_controller(err, 1, D1_max, 0)`. In the linear region (`|err| ≤ D1_max/P² = 2.5 m`) this
  is `err * 1`, which is exact. The error clamps `_error_min/max` are far away.
- o4. `* get_control_gain_scaler_Z() (= 1)` is exact. The additions of `_vel_desired`,
  `_vel_offset`, `_vel_terrain` (all `±0`) are exact.

`AC_PID_Basic.update_all` (`_pid_vel_d_m`: `P = 5`, `I = 0`, `D = 0`, `FF = 0`, `FLTE = 5 Hz`;
not in reset):
- o5. `fl(v_tgt - w_s)`.
- o6. `fl(· - E_v)`.
- o7. `fl(α_v · ·)`.
- o8. `E_v' = fl(E_v + ·)`.
- o9-o10. The derivative `(E_v' - E_v)/dt` and its 5 Hz filter. Not fed back (`D = 0`).
- `update_i` with `I = 0` sets the integrator to `0`, exactly.
- o11. `P_out = fl(E_v' · 5)`.
- `D_out = derivative · 0 = 0`; `+ 0 + 0 + target · 0` is exact.
- `· 1` (scaler) and `+ (_accel_desired + _accel_offset + _accel_terrain = 0)` are exact.

Acceleration measurement:
- o15. `a_meas = fl(f_s + GRAVITY_MSS)`, with `GRAVITY_MSS = 9.80665f = 5141509/2¹⁹`.
- The `IMAX` raise (`:1127-1129`) is not taken: hover `0.4444 < 0.8`.

`AC_PID.update_all` (`_pid_accel_d_m`: `P = 0.05`, `I = 0.1`, `D = 0`, `FF = 0`,
`IMAX = 0.8`, `FLTT = 0`, `FLTE = 20 Hz`, `FLTD = 0`; not in reset; `limit = false`):
- o16-o18. Target filter with `α_T = calc_lowpass_alpha_dt(dt, 0) = 1`:
  `_target = fl(_target_prev + 1 · fl(a_tgt - _target_prev))`. Two roundings and no memory.
- o19. `fl(_target - a_meas)`.
- o20. `fl(· - E_a)`.
- o21. `fl(α_a · ·)`.
- o22. `E_a' = fl(E_a + ·)`.
- The derivative and `_target_derivative` are computed but not fed back (`D = 0`, `D_FF = 0`).
- o26. `fl(E_a' · 0.1f)`.
- `· i_scale (= 1)` is exact.
- o28. `fl(· · dt)`.
- o29. `I' = fl(I + ·)`. The `constrain` to `±0.8` does nothing.
- o30. `P_out = fl(E_a' · 0.05f)`. `· Dmod (= 1)` and `· pd_scale (= 1)` are exact. `PDMX = 0`.
- o32. `fl(P_out + 0)` is exact. Then `out = fl(· + I')`.
- `+ get_ff() (= 0 + 0)` is exact.
- o34. `fl(out - MOT_THST_HOVER)`.
- `T = -(·)` is exact. `set_throttle_out` stores `T` (angle boost `× 1 × 1` is exact).

Next tick, `update_throttle_filter` (2 Hz):
- o36. `fl(T - F)`.
- o37. `fl(· · α_m)`.
- o38. `F' = fl(F + ·)`.
- The clip to `[0, 1]`, the mixer and the thrust curve are exact (section 1).

That is 30 rounded operations per tick on the path, plus three sensor readings and one constant
mismatch, `c = GRAVITY_MSS(float) - 9.80665 = 1.6174e-7`.

## 4. The states

States with memory at a hover sample, at the start of tick `t`:

| state | code | survives? |
|---|---|---|
| `z`, `w` | plant | yes |
| `sf` (stored specific force) | plant, `CState.sf` | yes, but `sf = -2.25 g F_{t-1}` after tick 0 (the actuator equals the filter output bit for bit), so it merges with `F` |
| `E_v` | `_pid_vel_d_m._error` | yes (5 Hz error filter) |
| vel-PID integrator | `_pid_vel_d_m._integrator` | no: `I = 0` writes `0` every tick |
| vel-PID derivative | `_pid_vel_d_m._derivative` | has memory, but `D = 0` keeps it out of the output (dead state) |
| accel-PID target filter | `_pid_accel_d_m._target` | no memory: `α_T = 1` |
| `E_a` | `_pid_accel_d_m._error` | yes (20 Hz error filter) |
| `I` | `_pid_accel_d_m._integrator` | yes |
| accel-PID derivative | `_derivative`, `_target_derivative` | `FLTD = 0` makes them memoryless functions of `E_a` and `_target`; `D = D_FF = 0` keeps them out of the output |
| `F` | `_throttle_filter_value` | yes (2 Hz filter) |
| `T` | `_throttle_in` (the one-tick delay) | a function of the same tick's state: `T_{t-1} = H - kp E_{a,t-1} - I_{t-1}`, up to rounding |
| others | `_vel_d_control_ratio`, `_limit_vector`, `_pid_info` | not fed back |

The eight-state recurrence `(z, w, sf, E_v, E_a, I, F, T)` has two eigenvalues at `0`: the `sf`
and `T` identities above hold after one step. Its other six eigenvalues are those of the
six-state recurrence below. I checked this numerically for the seven-state form with `T`:
eigenvalue `1.0e-17`, the other six identical.

Coordinates of the minimal recurrence, with `H` the exact value of `MOT_THST_HOVER` as a `float`
(`7455795/2²⁴ = 0.44440001249`):

`x = (ζ, w, Ev, Ea, ι, φ)`, where `ζ = z + 1`, `w` is the vertical velocity, `Ev = E_v`,
`Ea = E_a`, `ι = I - I*` with `I* = H - 4/9 = -4.4432e-5`, and `φ = F - 4/9`.

With this `I*` the hover is an exact equilibrium of the exact recurrence for any `H`. The
mismatch between `MOT_THST_HOVER` and the true `1/2.25` only moves the integrator's equilibrium.

## 5. The exact recurrence

Constants: the exact real values of the `Float32` constants the code computes. I evaluated them
with `Copter`'s own functions in Lean (`calc_lowpass_alpha_dt`, `Float32.ofNat 2500 * 1.0e-6`)
and cross-checked them bit for bit with `numpy.float32`.

| symbol | code | bits | exact | decimal |
|---|---|---|---|---|
| `dt` | `float(2500) * 1e-6f` (also `1/400.0f`) | `992204554` | `5368709/2³¹` | `0.0024999999441` |
| `α_v` | `calc_lowpass_alpha_dt(dt, 5)` | `1033183978` | `4886901/2²⁶` | `0.0728204995394` |
| `α_a` | `calc_lowpass_alpha_dt(dt, 20)` | `1047841643` | `16042859/2²⁶` | `0.2390572279692` |
| `α_m` | `calc_lowpass_alpha_dt(dt, 2)` | `1022985527` | `16352567/2²⁹` | `0.0304590296000` |
| `kp` | `PSC_D_ACC_P = 0.05f` | `1028443341` | `13421773/2²⁸` | `0.0500000007451` |
| `ki` | `PSC_D_ACC_I = 0.1f` | `1036831949` | `13421773/2²⁷` | `0.1000000014901` |
| `kv` | `PSC_D_VEL_P = 5.0f` | | `5` | |
| `kpos` | `PSC_D_POS_P = 1.0f` | | `1` | |
| `G` | `GRAVITY_MSS` | `1092413450` | `5141509/2¹⁹` | `9.8066501617` |
| `H` | `MOT_THST_HOVER 0.4444` | `1055098982` | `7455795/2²⁴` | `0.4444000125` |

Plant constants: `h = 1/400`, `g = 980665/100000`, `k = 2.25 g = 22.0649625`, so
`k · 4/9 = g` exactly.

One tick in the order of the code (Lean: `CopterVert.step`; with perturbations, `stepN`):

```
Ev' = (1 - α_v) Ev + α_v (-kpos ζ - w)                 + n1
Ea' = (1 - α_a) Ea + α_a (kv Ev' + k φ)                 + n2
ι'  = ι + ki dt Ea'                                     + n3
φ'  = (1 - α_m) φ + α_m (-kp Ea - ι)                    + n4
w'  = w - k h φ'
ζ'  = ζ + h w
```

Notes on the equations:
- The measured acceleration in `Ea'` is `f + g = -2.25 g u_{t-1} + g = -k φ` (old `φ`), and the
  accelerometer target is `kv Ev'`.
- `-kp Ea - ι` is the stored throttle of the previous tick minus `4/9`.
- `w'` uses the new actuator `φ'`.

As a matrix, `x' = A x + B n` with `n = (n1, n2, n3, n4)`:

```
A =
 [ 1           2.5e-3       0            0             0             0            ]
 [ 0           1            0            8.40096695e-5 1.68019336e-3 -5.34822129e-2]
 [-7.28204995e-2 -7.28204995e-2 9.27179500e-1 0          0             0            ]
 [-8.70413338e-2 -8.70413338e-2 1.10824481   7.60942772e-1 0           5.27478877   ]
 [-2.17603333e-5 -2.17603333e-5 2.77061199e-4 1.90235692e-4 1           1.31869718e-3]
 [ 0           0            0            -1.52295150e-3 -3.04590296e-2 9.69540970e-1]

B =  (columns n1, n2, n3, n4)
 [ 0             0             0   0             ]
 [ 0             0             0   -5.51624063e-2]
 [ 1             0             0   0             ]
 [ 1.19528614    1             0   0             ]
 [ 2.98821533e-4 2.49999998e-4 1   0             ]
 [ 0             0             0   1             ]
```

The same rows as exact formulas:
- `A_ζ = (1, h, 0, 0, 0, 0)`;
- `A_Ev = (-α_v kpos, -α_v, 1-α_v, 0, 0, 0)`;
- `A_Ea = α_a kv A_Ev + (0, 0, 0, 1-α_a, 0, α_a k)`;
- `A_ι = e_ι + ki dt A_Ea`;
- `A_φ = (0, 0, 0, -α_m kp, -α_m, 1-α_m)`;
- `A_w = e_w - k h A_φ`.

The exact rational `A` is what `gen.py` used. Lean checks that `CopterVert.step` is this `A` by
`ring` inside `contr_sos`.

**Validation against the Lean executable.** `closedloop.py` drives `.lake/build/bin/copter
--exact` line by line with the exact vertical plant (z, w, specific force from the last actuator).
`compare.py` then runs the recurrence from the state after the first tick. The first tick is the
`D_init_controller` reset:
- `E_v = -ζ - w` (unfiltered);
- `E_a = 5E_v - a_meas`;
- `I = ki dt E_a` (the set integrator is `0`);
- `F = T = H`.

For `MOT_THST_HOVER` = `0.4444`, `0.444` and `0.44`, the code's actuators over 4000 ticks (10 s)
match the recurrence within `3.4e-7`, `3.4e-7` and `3.6e-7`. The signal `max|u - 4/9|` is
`4.4e-5`, `4.4e-4` and `4.4e-3`. The difference does not grow with the signal, so it is the
accumulated rounding: the model is the code. At `0.43` the navigator moves its target (section
11), so that run does not test the recurrence.

## 6. Eigenvalues of `A`

| eigenvalue | modulus | decay rate (`-400 ln|λ|`) |
|---|---|---|
| `0.9974337906` | `0.9974337906` | `1.028 /s` |
| `0.9962565461 ± 0.0053526061 i` | `0.9962709250` | `1.494 /s` (oscillating at `2.14 rad/s`) |
| `0.9556056055` | | `18.16 /s` |
| `0.8998111087` | | `42.23 /s` |
| `0.8122996459` | | `83.15 /s` |

The loop is stable with spectral radius `0.99743` per tick. The slow modes, with time constant
about 1 s, come from the 2 Hz throttle filter inside the acceleration loop.

## 7. Lyapunov function

**Search.** I solved the discrete Lyapunov equation `(A/r)ᵀ P (A/r) - P = -Q`, which gives
`Aᵀ P A ⪯ r² P`. Nelder-Mead chose `r` and a diagonal `Q` to maximize the invariance margin of
section 8 for the box `|ζ| ≤ 1 cm`, `|w| ≤ 1 cm/s`. The optimum is `r = 0.997461` and
`Q = diag(4.95e-4, 2.56e-3, 4.63, 1.83e-2, 3.32e-3, 210.2)`, with

```
P_num =
 [ 9215.30   3309.69   296.014   20.5115   12273.7   -1571.68 ]
 [ 3309.69   3214.06   207.524   17.7646   -1089.23  -2790.30 ]
 [ 296.014   207.524   82.4123   2.65119   1480.44   -162.908 ]
 [ 20.5115   17.7646   2.65119   0.235036  45.6950   -22.5371 ]
 [ 12273.7   -1089.23  1480.44   45.6950   158994.   13267.8  ]
 [ -1571.68  -2790.30  -162.908  -22.5371  13267.8   5620.55  ]
```

**Rationalized.** I rounded every entry to two significant digits (`ratP.py` tried 2-6 digits
at `ρ = 0.995` and `0.996`; two digits pass at `0.996`):

```
P = [[ 9200,  3300,   300,    21,  12000, -1600],
     [ 3300,  3200,   210,    18,  -1100, -2800],
     [  300,   210,    82, 27/10,   1500,  -160],
     [   21,    18, 27/10,  6/25,     46,   -23],
     [12000, -1100,  1500,    46, 160000, 13000],
     [-1600, -2800,  -160,   -23,  13000,  5600]]
```

`V x = xᵀ P x` in `(ζ, w, Ev, Ea, ι, φ)`. This is `CopterVert.V`.

**Exact checks** (`cert.py`, `Fraction`):
- `P ≻ 0`. The `LDLᵀ` pivots are `9200, 2016.30, 67.0178, 0.104879, 98862.3, 1210.57`.
- `(249/250) P - Aᵀ P A ≻ 0`. Its `LDLᵀ` pivots are all positive; the smallest is `0.01704`.
  Pivots of up to 136 digits are exact rationals.
- So **`ρ = 249/250 = 0.996`** is certified: `V(Ax) ≤ 0.996 V(x)`, and `√ρ = 0.997998`. The
  numerical contraction of this `P` is `0.995379`.
- In Lean, `contr_sos` is the exact identity `(249/250) V x - V(step x) = Σ Dᵢ (Lᵀx)ᵢ²`, proved by
  `ring`, and `contr` follows by `positivity`. No `nlinarith` or `polyrith` is involved.

**Sublevel set and box.** The ellipsoid `{V ≤ γ}` gives `max |xᵢ| = √(γ (P⁻¹)ᵢᵢ)`. With the
exact `P⁻¹`, `|w| ≤ 1/100` needs `γ ≤ 0.101452` and `|ζ| ≤ 1/100` needs `γ ≤ 0.465393`. I chose
**`γ = 1/10`**. On `{V ≤ 1/10}`:

| state | bound | Lean |
|---|---|---|
| `ζ` | `0.004635` m | `bound_0`: `≤ 1/200` |
| `w` | `0.009928` m/s | `bound_1`: `≤ 1/100` |
| `Ev` | `0.04755` m/s | `bound_2`: `≤ 1/20` |
| `Ea` | `1.2901` m/s² | `bound_3`: `≤ 13/10` |
| `ι` | `0.0013765` | `bound_4`: `≤ 7/5000` |
| `φ` | `0.0090888` | `bound_5`: `≤ 1/100` |

These bounds also keep every saturation of the path inactive:
- throttle `4/9 + τ ∈ [0.38, 0.51] ⊂ (0, 1)`, with `|τ| ≤ 0.0645`;
- `|I| ≤ 0.0015 < IMAX = 0.8`;
- `sqrt_controller` linear for `|ζ| ≤ 2.5 m`;
- no `limit` flags, so no anti-windup.

## 8. Perturbations: budget, slack, verdict

**Slack.** If `V(x) ≤ γ`, then `√V(Ax + Bn) ≤ √ρ √γ + ‖Bn‖_P`. So the sublevel set is invariant
whenever

`‖Bn‖_P ≤ (1 - √ρ) √γ = (1 - 0.997998) · 0.316228 = 6.331e-4`.

Taken one at a time, the largest admissible perturbations are:
- `|n1| ≤ 6.68e-5`;
- `|n2| ≤ 1.21e-3`;
- `|n3| ≤ 1.58e-6`;
- `|n4| ≤ 8.23e-6`.

**binary32 budget** on `{V ≤ 1/10}` (`budget.py`). The magnitudes of every operand come from the
ellipsoid bounds of the linear functionals involved, plus a margin:

| perturbation | where | dominant parts | bound |
|---|---|---|---|
| `n1` (velocity error filter) | s1, s2, o1-o8 | `α_v` × (sensor `2⁻²⁴|w| ≤ 5.9e-10`, `z` through binary64 and the narrowing `2.8e-10`, o5-o6), plus o7-o8 at `2⁻²⁴ · 0.044` | `3.22e-9` |
| `n2` (accel error filter) | s3, o11, o15-o22, `c` | `α_a` × (`2⁻²⁴|f| = 5.96e-7` for `f ≈ -9.8`, plus `c = 1.62e-7`), plus o22 at `2⁻²⁴ · 1.0` | `3.00e-7` |
| `n3` (integrator) | o26, o28, o29 | `2⁻²⁴ · |I'|`, with `|I'| ≤ 1.4e-3` | `1.07e-10` |
| `n4` (throttle filter) | o30-o34 of the previous tick, o36-o38 | `α_m · e_T` with `e_T ≤ 3.63e-8` (o34 at `2⁻²⁴ · 0.51`), plus o38 at `2⁻²⁴ · 0.45` (`2.70e-8`) | `2.83e-8` |

Over the box of perturbations `|nᵢ| ≤ budgetᵢ` (all 16 vertices), the worst case is
`‖Bn‖_P = 2.289e-6`. **Margin: `6.331e-4 / 2.289e-6 = 277`.**

**Verdict.** The 1 cm hover box, in the form `|ζ| ≤ 5 mm` and `|w| ≤ 1 cm/s`, is provable at
binary32 with a factor of about 277 to spare. No looser box is needed.

Most of the budget does not scale with the state: the accelerometer reading of `-9.8` (about
`6e-7`), the gravity constant (`1.6e-7`) and the throttle level (about `2.7e-8`). The box
therefore shrinks almost in proportion. With this `P`, the smallest square box for which the
argument closes is `|w| ≤ 3.37e-5 m/s` (with `|ζ| ≤ 1.57e-5 m`): about 34 µm/s and 16 µm. For
the 1 cm box the binary32 rounding is not the bottleneck.

**What Lean proves** (`lyap_stepN`) uses deliberately generous bounds,
`NBound: |n1| ≤ 1e-8, |n2| ≤ 1e-6, |n3| ≤ 1e-9, |n4| ≤ 1e-7`. That is 3.1, 3.3, 9.3 and 3.5 times
the budget. The bounds pass through `pert`:
- `|m_w| ≤ 1e-8`;
- `|m_Ev| ≤ 1e-8`;
- `|m_Ea| ≤ 1.2e-6`;
- `|m_ι| ≤ 2e-9`;
- `|m_φ| ≤ 1e-7`.

The proof then uses `V(y + m) ≤ (501/500) V(y) + 501 V(m)` (`V_pert`) and the termwise bound
`V(m) ≤ Σ |P_ij| μᵢ μⱼ ≤ 1e-10` (`V_small`; the exact value is `7.48e-11`). The inequality
`(501/500)(249/250)(1/10) + 501 · 1e-10 = 0.0997993 ≤ 1/10` holds. The argument would still
close with the `μ` scaled up by 73.

## 9. What is proved in Lean

`lake build Contracts.CopterPlant Contracts.CopterVert` passes, with no `sorry`. The axioms are
only `propext`, `Classical.choice` and `Quot.sound`.

`Contracts/CopterPlant.lean`:
- `CState`, `dynR` (real thrust fractions), `dyn` (the `Vector Float32 4` actuators through the
  linear configuration), `quatOf`, `sample` (to `Copter.AHRS.Sample`), `plant`, `CX`, `Mplant`.
- The port hypotheses `Sense32Spec`, `SensePSpec` and `CopterSense`.
- `kf_maxRPM_sq`.
- `thrust_div_mass`.
- `dynR_vert` and `dyn_vert`: four equal actuators move a level state at rest only along the
  vertical, with `sf' = -2.25 g c`.
- `dynR_hover`: at `1/2.25` the hover state is fixed.
- `quatOf_level`.
- `sample_vstate`: the sample of a vertical state is zeros, `(1,0,0,0)` and the vertical
  readings.

`Contracts/CopterVert.lean`:
- The constants, `VX`, `step`, `stepN`, `pert`, `stepN_eq`, `step_zero`.
- `V`, `V_sos` and `V_nonneg`.
- `contr_sos` and `contr` (`V (step x) ≤ 249/250 · V x`).
- `V_sos_i` and `bound_i` for all six coordinates.
- `V_pert`, `term_le_pos`, `term_le_neg`, `V_small`, `NBound`, `pert_small`.
- `lyap_stepN`: `V ≤ 1/10` is invariant under `stepN` with `NBound`.
- `box_of_V`.
- `vert_invariant`: a sequence that follows `stepN` with `NBound` perturbations whenever it is in
  `{V ≤ 1/10}` stays there, with `|ζ| ≤ 1/200` and `|w| ≤ 1/100`, for all `t`.

`Contracts.lean` does not import the two files; I was not allowed to edit it. `lake build` with
the module names builds them.

## 10. Plan for the `Float32` perturbation lemmas (not done in this phase)

1. **Constants.** Prove the `toReal` of `dt`, `α_v`, `α_a`, `α_m`, `0.05f`, `0.1f`,
   `GRAVITY_MSS` and `MOT_THST_HOVER` equal the rationals of section 5. The literals follow from
   their bit patterns (as `QuadHover.near_lit` does for binary64). The computed constants
   (`calc_lowpass_alpha_dt`, `float(2500) * 1e-6f`) need the binary32 model of `/`, `+` and `*`
   (`FloatModel.Float32`) evaluated at those arguments.
2. **Inductive invariant**, the analogue of `QuadHover.InvC`. The PID states are not in reset.
   The vel-PID integrator is `0`. The accel-PID `_target` is finite and within `|a_tgt_prev|`
   bounds. The stored throttle `T_f` satisfies
   `|T_f - (4/9 - kp Ea - ι)| ≤ 3.7e-8`, with `Ea`, `ι` the `toReal` of the stored floats.
   `F_f` is the actuator, and `sf = -k (F_f - 4/9) - g` holds for the plant.
3. **One-tick lemma.** At a hover sample with `V(x) ≤ 1/10` and `CopterSense`, the `Float32`
   `D_update_controller` and the next `output` produce floats whose `toReal` is `stepN x n` for
   some `n` with `NBound n`, and they re-establish the invariant of step 2. Do it operation by
   operation, with the `Near` calculus ported to `Float32`, as `QuadHoverVert.posZ_near` and
   `thrust_near` did for the old controller. The bounds needed are the section-8 budget, with a
   factor of at least 3 to spare.
4. **Composition.** With the zero half (exact zeros horizontally and in rotation, actuators all
   equal) and `CopterPlant.dyn_vert`, the closed loop's vertical state follows `stepN`.
   `vert_invariant` then gives the 5 mm / 1 cm/s box.
5. **First tick.** The initial tick is the `D_init_controller` reset (section 5). Either show that
   the state after it lies in `{V ≤ 1/10}`, or start the induction at tick 1. `Copter.takeover`
   sets `F = T = H`. The plant must start with `sf = -k (H - 4/9) - g`, the specific force of the
   actuator `H`; for exact consistency use that rather than `-g`. Otherwise add the one-tick
   discrepancy as an extra perturbation.

## 11. Caveats found on the way

- **The navigator target is not always fixed near the hover.** With the hover mission and
  `MOT_THST_HOVER` = `0.43` or `0.42`, in runs started level at the waypoint and at rest, AC_WPNav
  starts moving the position target at tick 1 (`_vel_desired.z = 0.0025`,
  `_accel_desired.z = 1.0`). The first tick has already produced `w ≈ 8e-4 m/s` and `1.35e-3`.
  It comes to rest 0.8 mm (0.43) and 1.35 mm (0.42) away from `-1`; in the 0.42 run it is at rest by tick 50. With
  `0.44`, `0.444` and `0.4444` (`w_1 ≤ 2.5e-4`) the target stayed at exactly `-1` for 4000
  ticks, even though `|w|` later reached `9.7e-3`. So some navigator path is sensitive to the
  early velocity (the `SCurve`/offset logic of `AC_WPNav.update_wpnav`, not traced further). The
  hover proof's navigator lemma must show the target stays fixed on the whole box, or the box
  must exclude this.
- `CopterSense` asks for `sense32 1 = 1`, `sense32 0 = +0` and `senseP 0 = +0`, so that the level
  quaternion and the zero horizontal readings are exact. Round to nearest satisfies all three. No
  concrete binary32 sensor has been proved to meet `Sense32Spec` yet; for binary64 the
  analogue is `FloatLoopIEEE.senseNearest`.
- The budget treats `c = G_f - g` and the sensor error of `f` separately. At exactly `f = -g`
  they cancel (`sense32(-9.80665) = -G_f`), so the budget is conservative there.
- `MOT_THST_HOVER` enters only through `I* = H - 4/9`. Any `H < IMAX = 0.8` with `|I*|` well
  inside `0.8` gives the same recurrence.
