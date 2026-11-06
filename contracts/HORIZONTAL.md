# The horizontal channel (milestone M6, discrete-time part)

This note documents `Contracts/Track/Horizontal*.lean`, the discrete-time real-valued part of
milestone M6 of TRACK_PLAN.md. It covers:

* the linear model of the horizontal channel, per axis, with the attitude loop abstracted by an
  interface;
* its Lyapunov certificate;
* the certified error response to the S-curve legs 1–7 of the mission;
* the corner (transfer) property T4 at `w₁ … w₆`.

The connection to the float code (the C-series lemmas) and the attitude contract (M4) are not part
of this milestone. Section 7 states the interface the theorems need.

Everything is sorry-free. `#print axioms` shows only `propext`, `Classical.choice` and
`Quot.sound` (AxiomCheck.lean, end of file). The kernel checks use `decide +kernel`, not
`native_decide`.

## 0. Results

| quantity | value | Lean |
|---|---|---|
| controller law vs. recorded command (`thr_n`, `thr_e`) | 4.5·10⁻⁷ m/s² at every tick (exact law) | Python, §2 |
| model vs. recorded flight (`lean-course-1ms`) | max \|Δe\| 6.5 mm (N), 6.0 mm (E); rms 2.6 / 2.3 mm | Python, §2 |
| ideal S-curve legs vs. recorded `vsp`/`asp` (through the corners) | 2.6·10⁻⁴ m/s² at equal velocity, blend start fitted | Python, §3 |
| spectral radius of `Ah` | 0.999579 (the PID integrator, time constant 6 s) | |
| contraction factor | `λ_h = 0.9997` | `V_A` |
| Lyapunov matrix | `Ph` symmetric positive definite (9×9 integers, cond 5.6·10⁴) | `Ph_posDef`, `certV` |
| output weight | `e² ≤ γ V`, `γ = 1.201·10⁻¹¹` | `sq_e_le` |
| course legs 1–7, from zero error | **`√(eN² + eE²) ≤ 0.0285 m`** at every tick | `course_norm` |
| corner `w₁ … w₆`, target within 0.1075 m (= 0.105 + 2.5 mm) | vehicle (model) within **0.0841 m** (check 0.08409, at w₄) | `corner_vehicle` |
| same, per corner w₁ … w₆ | 0.08143, 0.08240, 0.08300, 0.08409, 0.08258, 0.08280 (+2·10⁻⁷) | `corner_vehicle_per` |
| corner, target within 0.105 m | 0.08075 (check 0.08074, at w₄); per corner 0.07841 … 0.08074 | `corner_vehicle_105`, `corner_vehicle_per_105` |
| T4 for the real target and vehicle | holds if target ≤ 1 mm and error ≤ **15.9 mm** from the nominal | `corner_transfer` |
| kernel time | 36 s per axis (trajectories), about 25 s checks, 2.4 s certificate | §6 |

Python gives a maximum of 0.02844 m for the same model and reference. The recorded flight's
maximum is 0.0300 m. Combined with the vertical channel, the climb peak 0.0875 m (VERTICAL.md) is
on leg 0. Even if both peaks fell on the same tick, `√(0.0875² + 0.0285²) = 0.0920 < 0.095`.

## 1. The model (`Horizontal.lean`)

**Channel split.** The position controller is rotation-equivariant, and the attitude loop is
abstracted per axis. The north and east axes therefore have the same matrices. One axis has nine
states `ξ = (e, ev, E, D, I, a, c₁, c₂, c₃)`:

| # | state | code variable |
|---|---|---|
| 0 | `e = p - sp` | plant position against `_pos_target_ned_m` (this axis) |
| 1 | `ev = v - vsp` | plant velocity against `_vel_desired_ned_ms` |
| 2 | `E` | `_pid_vel_ne_m._error` (5 Hz filter) |
| 3 | `D` | `_pid_vel_ne_m._derivative` (5 Hz filter of `(E⁺ - E)/dt`) |
| 4 | `I` | `_pid_vel_ne_m._integrator` |
| 5 | `a` | the horizontal acceleration the vehicle realizes over the period (attitude interface) |
| 6–8 | `c₁, c₂, c₃` | the acceleration commands `_accel_target_ned_mss` of 1, 2, 3 ticks ago |

**Tick.** `tick` follows `NE_update_controller`, one statement per `let`:

1. `AC_P_2D::update_all` (linear branch of `sqrt_controller`): `vt = kpPos (sp - p) + vsp`;
2. `AC_PID_2D::update_all`:
   * `E⁺ = E + αE ((vt - v) - E)`;
   * `D⁺ = D + αE ((E⁺ - E)/dt - D)`;
   * `I⁺ = I + ki dt E⁺` (`update_i` runs after the filters, with the new error);
3. the command `c = kp E⁺ + I⁺ + kd D⁺ + asp`. `limit_accel_xy` is inactive, and `c` is the
   horizontal part of `get_thrust_vector`;
4. **the attitude interface**: `a⁺ = a + αL (c₃ - a)`, a first-order lag with a three-tick delay;
5. the plant (exact double integrator over the period): `p⁺ = p + h v + h²/2 a`, `v⁺ = v + h a`.

**Theorems.**

* `tick_eq` proves `tick ξ asp d₁ d₂ = Ah ξ + asp Bh - d₁ e₀ - d₂ e₁`. The defects
  `d₁ = sp' - sp - h vsp - h²/2 asp` and `d₂ = vsp' - vsp - h asp` are those of the target sequence.
* `errOf_absTick` and `errResp_eq_code` prove that the code's variables (`HAbs`, `absTick`) become
  this system in error coordinates.
* `errOf_traj_dist` proves that a disturbed tick `Ah ξ + forceOf r + w` stays the certified
  response plus the free response to `w`.

**Constants.** They are exact rationals, taken as the float32 values the code computes:

* `αE = calc_lowpass_alpha_dt(0.0025f, 5) = 4886901/2²⁶`, used for both filters (`FLTE = FLTD = 5`);
* `dt = 0.0025f = 5368709/2³¹`;
* `kpPos = 1.5`, `kp = 6`, `ki = 1`, `kd = 0.5`, from `copter-cf2x-tuned.txt` and the
  `AC_PID_2D` defaults;
* `h = 1/400` (`per_eq`);
* the interface constants `αL = 13/500` (time constant 0.095 s) and the delay `dL = 3` ticks.

```
Ah = 1         0.0025    0         0        0  3.125e-06  0  0  0
     0         1         0         0        0  0.0025     0  0  0
    -0.109231 -0.0728205 0.92718   0        0  0          0  0  0
    -3.1817   -2.12113  -2.12113   0.92718  0  0          0  0  0
    -2.73e-04 -1.82e-04  2.318e-03 0        1  0          0  0  0
     0         0         0         0        0  0.974      0  0  0.026
    -2.24651  -1.49767   4.50483   0.46359  1  0          0  0  0
     0         0         0         0        0  0          1  0  0
     0         0         0         0        0  0          0  1  0
Bh = (-3.125e-06, -0.0025, 0, 0, 0, 0, 1, 0, 0)
eig Ah = 0.999579, 0.993678, 0.989042, 0.976343 ± 0.02183 i, 0.893014, 0.010842, -0.010483, 0
```

The constant-acceleration feedforward is exact. A step of `asp` therefore leaves no steady-state
error. The step response peaks at -0.0137 m per m/s² after 148 ticks.

## 2. Validation against `sim/out/lean-course-1ms/flight.csv`

Scripts are in
`/private/tmp/claude-501/-Users-ryan-Research-delegate/547e050f-c29a-418f-816a-16412bc752a6/scratchpad/horiz6/`.

**Controller law** (`ctrlcheck.py`). The law of items 1–3, applied to the recorded plant state
`(x_n, vx_n)`, `(y_e, vy_e)` and the recorded target, reproduces the recorded command
`thr_n`, `thr_e` to 4.5·10⁻⁷ m/s² at every tick from tick 2. It uses `reset_filter` on tick 0 and
`I = 0`. The law is exact; its residual is float rounding.

**Attitude interface** (`fitlag.py`, `closedloop.py`, `val2.py`). The realized acceleration over a
period is `(v_{k+1} - v_k)/h` from the recorded velocity. To fit the lag, the closed-loop model
(exact law, lag interface, exact plant) was driven by the recorded target from the recorded state
at tick 12, and its position error was compared with the recorded one.

| `αL` | `dL` | max \|Δe\| N / E | rms N / E | model max \|e\| N / E |
|---|---|---|---|---|
| **13/500** (τ = 0.095 s) | **3** | **6.5 / 6.0 mm** | **2.6 / 2.3 mm** | 2.84 / 2.73 cm |
| 13/500 | 2 | 6.7 / 5.9 mm | 2.7 / 2.3 mm | 2.76 / 2.65 cm |
| 13/500 | 4 | 6.5 / 6.3 mm | 2.7 / 2.3 mm | 2.93 / 2.81 cm |
| 27/1000 | 3 | 6.8 / 6.1 mm | 2.6 / 2.3 mm | 2.73 / 2.62 cm |

The recorded maximum is 3.00 / 2.97 cm. The residual is concentrated in the 90° yaw turns at the
corners (yaw rate ±1.05 rad/s): its sign follows the turn direction. This is the heading coupling
of TRACK_PLAN.md 3.3, which is not part of the per-axis model.

Two alternatives do not reduce the residual:

* a second lag (two cascaded first-order lags, with any delay): 6.3–6.7 mm;
* rotating the lag with the measured yaw (lag in the body frame): 12 mm.

The acceleration discrepancy `η = a_real - a_lag` reaches 0.26 m/s² (rms 0.07). Section 7 discusses
what that means for the tube.

## 3. The reference: S-curve legs 1–7 (`scurve.py`, `course.py`)

### 3.1 The leg profiles from `calculate_path`

`calculate_track` gives, for each leg (straight geometry, no arcs):

* `vel_max = kinematic_limit(L_ne, Δz, WP_SPD = 1, 2.5, 1.5)`;
* `accel_max = kinematic_limit(L_ne, Δz, WP_ACC = 1.5, WP_ACC_Z = 1, 1)`.

The horizontal limit binds on every leg, so the horizontal speed is exactly 1 m/s and the
horizontal acceleration exactly 1.5 m/s². The per-axis acceleration of one leg is `±1.5/√2`.

`calc_scurve_jerk_and_snap` gives `Jm = WP_JERK = 5` and `Sm = 5π/(2·0.1)/2`, hence `tj = 0.2 s`.
`add_segments(L)` then calls `calculate_path(Sm, 5, 0, Am, Vm, L/2)`, which takes the
`|At| ≥ Jm tj` branch (velocity-limited):

* `t2 = t6 = Am/Jm - tj`;
* `t4 = (Vm - Am tj - Am²/Jm)/Am`.

The acceleration phase is: raised-cosine jerk up (`tj`), constant jerk (`t2`), jerk down (`tj`),
constant acceleration (`t4`), then the mirror image. The cruise `t15` fills the length.

| leg | L (m) | Am | Vm | t2 | t4 | T (s) | t_acc | t_dec | start tick |
|---|---|---|---|---|---|---|---|---|---|
| 1 | 1.77904 | 1.50957 | 1.00638 | 0.10191 | 0.16475 | 2.93635 | 1.16858 | 1.76777 | 0 |
| 2 | 1.77904 | 1.50957 | 1.00638 | 0.10191 | 0.16475 | 2.93635 | 1.16858 | 1.76777 | 740 |
| 3 | 1.77904 | 1.50957 | 1.00638 | 0.10191 | 0.16475 | 2.93635 | 1.16858 | 1.76777 | 1480 |
| 4 | 3.54119 | 1.50240 | 1.00160 | 0.10048 | 0.16619 | 4.70268 | 1.16715 | 3.53553 | 2221 |
| 5 | 1.77904 | 1.50957 | 1.00638 | 0.10191 | 0.16475 | 2.93635 | 1.16858 | 1.76777 | 3669 |
| 6 | 1.79304 | 1.52145 | 1.01430 | 0.10429 | 0.16238 | 2.93872 | 1.17096 | 1.76777 | 4409 |
| 7 | 1.79304 | 1.52145 | 1.01430 | 0.10429 | 0.16238 | 2.93872 | 1.17096 | 1.76777 | 5149 |

### 3.2 The corner blends

`SCurve::advance_target_along_track` with fast waypoints starts the next leg at the first tick
where all of the following hold:

* the current leg is past its deceleration start;
* its remaining time is at most the next leg's acceleration time;
* the predicted turn point (both legs at half the remaining time) is within `wp_radius = 0.1`;
* the turn speed and acceleration are below the limits.

The next leg then contributes with time `h` on that tick. The target is the sum of the legs'
contributions. On the axis that reverses, the corner acceleration therefore peaks at
`2 · 1.5/√2 = 1.5√2 ≈ 2.1213 m/s²`. On the other axis the two legs nearly cancel and leave a
±0.29 m/s² dip. The reference class therefore has `|a_ref| ≤ 1.5√2` per axis; the corner sums are
part of the table. With an ideal time base, the legs start at the ticks of the table above, from the
start of leg 1. The course ends (at rest at `w₇ = w₀`) at tick 6324.

### 3.3 Validation

`warpcmp2.py` compares the recorded `asp` with the ideal profile at equal velocity (2D), which does
not depend on the time warp. Through each corner window:

| corner | w₁ | w₂ | w₃ | w₄ | w₅ | w₆ |
|---|---|---|---|---|---|---|
| ideal blend start: max \|ΔA\| (m/s²) | 1.3·10⁻² | 1.6·10⁻² | 5.8·10⁻³ | 7.0·10⁻³ | 7.1·10⁻³ | 1.7·10⁻² |
| fitted blend start (ticks later) | 1.44 | 1.80 | 0.66 | 0.80 | 0.80 | 1.94 |
| fitted: max \|ΔA\| (m/s²) | 2.2·10⁻⁴ | 2.1·10⁻⁴ | 2.2·10⁻⁴ | 2.0·10⁻⁴ | 2.6·10⁻⁴ | 7.1·10⁻⁵ |

So the leg profiles and the blend sum are confirmed through the corners. The only free quantity is
the start of each blend. In the flight it lies 0.7–1.9 ticks after the ideal-time rule: the
`|turn_pos| < 0.1` test is decided near its threshold (the corner cut is 0.1006 m), and the time
warp moves it. The recorded time base drifts by about 2.5 ticks over leg 1 (pacing, M8).

`blendpert.py` measures the effect of these offsets on the model:

| blend shifts (ticks) | max \|e\| | worst corner vehicle distance |
|---|---|---|
| 0 (ideal rule) | 0.02844 | 0.08074 |
| as fitted (1.44 … 1.94) | 0.02841 | 0.08115 |
| +2 each | 0.02839 | 0.08082 |
| -1 each | 0.02847 | 0.08040 |

The effect is below 0.5 mm, well inside the margins of §4.

## 4. The Lyapunov certificate (`HorizontalCertData.lean`, `HorizontalCert.lean`)

**Construction.** As for the vertical channel (`gen_cert.py`):

* `Ph` solves the Stein equation `(A/0.99968)ᵀ P (A/0.99968) - P = -I`, scaled so that
  `max P_ij = 10¹²`, and rounded to integers;
* `λ_h = 9997/10000`;
* `λ² Ph - Ahᵀ Ph Ah = Lc · diag Dc · Lcᵀ` with `min Dc = 2.7·10⁷`, the `L D Lᵀ` factorization in
  rationals (up to 1220 bits).

**Checks.** `certV`, `Dc_nonneg`, `certP`, `Dp_pos`, `Lp_mul_inv`, `certO` and `Do_nonneg` are
each one `decide +kernel`.

**Theorems.** These give `Ph_posDef`, `V_A`, `sq_e_le`, `V_iss`, `V_traj_le`, `e_traj_le` and
`e_traj_le_const`, with the same statements as the vertical ones on `Fin 9`.

The certificate is used for the rounding, the tail after the course and the tube, not for the
reference response. The ISS gain through it is about 100 m per m/s².

## 5. The course response (`HorizontalData.lean`, `HorizontalTraj{N,E}.lean`, `HorizontalChecks.lean`, `HorizontalCourse.lean`)

### 5.1 Method

The vertical climb used a family of bang-bang profiles and an averaging argument. The course is
handled differently: the model is driven by the course table itself.

1. **The table.** `gen_traj.py` evaluates the ideal course (§3) in double precision and rounds
   position, velocity and acceleration of each axis to the grid `2⁻⁴⁰ m` (error below 10⁻¹²),
   for ticks `0 … 6624`. The theorems are about this explicit table (`refN`, `refE`). It is at
   rest at the origin from tick 6324 on (`endN`, `endE`).
2. **The trajectory.** The floor-rounded recurrence `y⁺ = ⌊(Ahat y + inpH)/DAh⌋` is stored with
   the table entries (`V12` tuples with offset `2⁶²`), in 207 chunks of 33 entries per axis.
   * `Ahat = DAh · Ah` (`Ahat_spec`);
   * `inpH = DAh · 2⁴⁰ · forceOf` of the table (`inpH_real`; `DAh` is the 90-bit common
     denominator).

   Each chunk's 32 transitions are one `decide +kernel` (`chunksN_ok`). Consecutive chunks share an
   entry (`chunksN_link`).
3. **Rounding.** `step_real` and `rounding_bound` show that the stored and the real response
   differ by a rounding disturbance below `2⁻⁴⁰` per tick. `V_iss` absorbs it:
   `V(errResp - y) ≤ Cδ` and `|e - y/2⁴⁰| ≤ 10⁻⁷` (`resp_close`; the true value is 2.2·10⁻⁸).
4. **Checks** (`HorizontalChecks.lean`):
   * `normOK`: `(10⁵ yN)² + (10⁵ yE)² ≤ (2845 · 2⁴⁰)²` at every stored tick;
   * `cornerOK`: for each corner and stored tick, if `|table target - w| ≤ 0.106` then
     `|table target + y - w| ≤ 0.083`, in integer arithmetic;
   * `tailN_check`, `tailE_check`: `γ V(y_K) ≤ 0.008²` at the last tick.
5. **After the course.** From tick `Kh = 6624` on, the forcing is zero (`forceOf_rest`). `V` does
   not increase along the free motion, and Young's inequality gives `|e| ≤ 0.00805`
   (`resp_tail`).

### 5.2 Statements

* `course_norm : errN k ^ 2 + errE k ^ 2 ≤ 0.0285 ^ 2` for every tick `k`. Its per-axis
  consequences are `course_N` and `course_E`.
* `corner_vehicle (i : Fin 6) m`: if `hyp (tN m - cN i) (tE m - cE i) ≤ 0.1075`, then
  `hyp (tN m + errN m - cN i) (tE m + errE m - cE i) ≤ 0.0841`. Here `hyp` is the Euclidean length
  and `(cN i, cE i)` are `w₁ … w₆` relative to `w₀`. After the course the target is at `w₀`, far
  from every corner, so those ticks are vacuous. The window `0.1075 = 0.105 + 2.5 mm` allows one
  whole tick of target travel at 1 m/s.
* `corner_vehicle_per`, `corner_vehicle_per_105`: the same per corner, at the windows `0.1075` and
  `0.105` (§5.4); `corner_vehicle_105`: `0.08075` at the window `0.105`; `corner_vehicle_106`:
  `0.0831` at the window `0.106`, which `corner_transfer` uses.
* `corner_transfer (i) m qN qE xN xE`: for any real target `q` and vehicle `x` at tick `m`, if
  * `|q - table target| ≤ 1 mm`,
  * `|(x - q) - (errN m, errE m)| ≤ 15.9 mm`, and
  * `|q - wᵢ| ≤ 0.105`,

  then `|x - wᵢ| ≤ 0.1`. This is T4 at `w₁ … w₆`, with the signed nominal error: the vehicle lags
  into the corner. An isotropic bound would need `0.105 + 0.0285 ≤ 0.1`, which fails.
* `course_tube`: for `ξ⁺ = Ah ξ + forceOf r + w` with `V(w) ≤ c`, the error is the certified
  response plus `√(γ (λᵏ V(ξ 0) + c/(1-λ)²))`. An initial horizontal state at the start of leg 1
  (corner starts of leg 0) enters through `V(ξ 0)`.

### 5.3 Numbers (same model, Python)

| corner | window 0.105 (ticks) | closest target | max vehicle distance | margin to 0.1 |
|---|---|---|---|---|
| w₁ | 941–971 | 0.10064 | 0.07840 | 2.16 cm |
| w₂ | 1681–1711 | 0.10064 | 0.07948 | 2.05 cm |
| w₃ | 2421–2453 | 0.10005 | 0.07990 | 2.01 cm |
| w₄ | 3868–3901 | 0.09969 | 0.08074 | 1.93 cm |
| w₅ | 4610–4641 | 0.10034 | 0.07960 | 2.04 cm |
| w₆ | 5351–5380 | 0.10076 | 0.07932 | 2.07 cm |

With the enlarged window 0.106 used in the check, the worst vehicle distance is 0.0823 (w₄), so
the certified 0.083 leaves 0.7 mm. The flight's margins are 2.08–2.35 cm. The model's are
1.93–2.16 cm: the model's error is slightly larger at the apex than the flight's.

### 5.4 Corner bounds for the 3D budget

The kernel checks (`cornerP_all`) give these tightest per-corner bounds, rounded up to 10⁻⁵ m.
The real statements add `2·10⁻⁷` for rounding.

| corner | w₁ | w₂ | w₃ | w₄ | w₅ | w₆ |
|---|---|---|---|---|---|---|
| planar, window 0.1075 (`BA`) | 0.08143 | 0.08240 | 0.08300 | **0.08409** | 0.08258 | 0.08280 |
| planar, window 0.105 (`BB`) | 0.07841 | 0.07948 | 0.07990 | **0.08074** | 0.07960 | 0.07933 |
| vertical \|ez\| on the window 0.1075, worst start (Python) | 0.01956 | 0.00151 | 0.00368 | 0.00699 | 0.00675 | 0.00480 |
| vertical, legs 1–7 alone (zero vertical state at leg 1, Python) | 0.00590 | 0.00180 | 0.00382 | 0.00700 | 0.00675 | 0.00480 |

**Where the vertical numbers come from** (`vert_corner.py`, `vert_leg0.py`, `vtail.py`). The
vertical model is that of VERTICAL.md. It is driven by leg 0, a vertical climb of length
`L ∈ [0.5, 0.835]` from the box, followed by the same blend rule into legs 1–7, whose vertical
components are 0.2–0.3 m per leg.

* **w₁:** the error there is the tail of the leg-0 climb, 1.09–1.96 cm, growing with `L`. The
  flight recorded 1.79 cm (`L = 0.7865`); the model gives 1.85 cm.
* **w₂ … w₆:** the vertical error is at most 7.0 mm and does not depend on the start.
* **Not certified.** The vertical values are Python only. A certified value at `w₁` needs the leg-0
  nominal for the whole start family, at the signed per-tick level. Bounding the leg-0 tail
  through `V_v` gives 6–9 cm at `w₁` (the condition of `P_v`). Through the ISS gain and `V_A` it
  gives 0.4 cm at `w₄`, 0.09 cm at `w₅`, 0.02 cm at `w₆`, but only under a hypothesis on the leg-0
  forcing. That is not the cheap single trajectory the request asked for, so it was not done.

**The 3D margin.** The formula is `√((P + 0.0025 + 0.007)² + (0.0131 + vz)²)` against `0.0954`,
with the worst-start `vz` above:

| planar `P` | w₁ | w₂ | w₃ | w₄ | w₅ | w₆ |
|---|---|---|---|---|---|---|
| uniform 0.0841 (window 0.1075) | -3.73 mm | +0.67 | +0.31 | -0.33 | -0.28 | +0.10 |
| per corner, window 0.1075 | -1.21 mm | +2.35 | +1.40 | -0.32 | +1.21 | +1.39 |
| per corner, window 0.105 | +1.63 mm | +5.23 | +4.44 | +2.95 | +4.12 | +4.79 |

The target bound `0.0815` at the window `0.1075` is not reachable. The model's own worst vehicle
distance there is 0.0840865, at w₄, tick 3864: the window reaches back to ticks where the vehicle
still lags along the incoming leg.

The window `0.1075` and the term `+0.0025` both stand for the one-tick target allowance. If
`+0.0025` in the formula already accounts for it, the window should stay `0.105`. With the
per-corner `BB` bounds, every corner then closes: the margins are 1.6–5.2 mm, and w₁ is the tightest
because of the leg-0 vertical tail.

## 6. Kernel time

Measured with `lake env lean -Dprofiler=true`; build times are those of `lake build`.

| file | build | type checking | content |
|---|---|---|---|
| `Horizontal.lean` | 4.2 s | | model, change of coordinates |
| `HorizontalCertData.lean` | 3.1 s | | rational matrices |
| `HorizontalCert.lean` | 4.6 s | 2.4 s | 7 kernel identities, real corollaries |
| `HorizontalData.lean` | 4.0 s | | encodings, row functions, `stepRows_spec` |
| `HorizontalTrajN.lean` | 74 s | **36 s** | 6624 transitions (5.4 ms each), elaboration 12 s |
| `HorizontalTrajE.lean` | 74 s | **36 s** | the same, east |
| `HorizontalChecks.lean` | 34 s | about 25 s | norm, corners (3 windows × 6 × 6831 entries), tails |
| `HorizontalCourse.lean` | 30 s | 0.6 s | soundness, `course_norm`, corners, tube |

**Encoding lessons**, in addition to VERTICAL.md §6:

1. **No `drop` into one long list.** A single 6625-entry list (as `l₀ ++ l₁ ++ …`) checked by
   `traj.drop (32 c)` took 175 s of kernel time. The same data as a list of 207 chunk lists, each
   reached by `getD c`, took 36 s. The walk to entry `32 c` through a long list of large tuples
   dominated.
2. **Literal size.** A flat literal of 6625 twelve-tuples exceeds `maxRecDepth` at elaboration. Use
   parts of at most about 400 entries (here 8 chunks of 33), with `maxRecDepth 100000` and
   `maxHeartbeats 0` on the definitions.
3. **Entry equality.** Equality of `ℕ`-tuples is not found by `Decidable` synthesis at this
   width. A Boolean `v12eq` with a soundness lemma is needed.
4. **Store the input with the state.** Keeping the table in the same tuple as the state, so each
   transition reads its own input, avoids a second walk.
5. **Zero coefficients.** Writing only the nonzero terms of `Ahat` helps (`Ah` has 25 nonzero
   entries of 81).

## 7. Interface to the controller lemmas, the attitude contract and the S-curve library

**What the theorems need.** The theorems are about the real model. To join them to the code, the
following facts are needed at every tick of legs 1–7 (on the region `D`, TRACK_PLAN.md 3.2). As in
VERTICAL.md, `⟦·⟧` is the real value of a float and `β` an explicit bound.

**C-series, `NE_update_controller`.** Preconditions:

* `NE_is_active`; no EKF reset; `_disturb_* = 0`; offsets zero; scale factors `1`;
* `|error| ≤ linear_dist` of `AC_P_2D` (`D1_max/kp²`) and `error_max` inactive (D6);
* `limit_accel_xy` inactive (`|accel_target| ≤ g tan(angle_max)`, D7), hence `_limit_vector = 0`
  and `update_i` without clamp;
* `|I| < 10` (D13).

Then, per axis:

* `⟦vt⟧ = kpPos (⟦pos_target⟧ - ⟦pos_est⟧) + ⟦vel_desired⟧ + β`;
* `⟦E⁺⟧ = ⟦E⟧ + αE ((⟦vt⟧ - ⟦vel_est⟧) - ⟦E⟧) + β`;
* `⟦D⁺⟧ = ⟦D⟧ + αE ((⟦E⁺⟧ - ⟦E⟧)/dt - ⟦D⟧) + β`;
* `⟦I⁺⟧ = ⟦I⟧ + ki dt ⟦E⁺⟧ + β`;
* `⟦accel_target⟧ = kp ⟦E⁺⟧ + ⟦I⁺⟧ + kd ⟦D⁺⟧ + ⟦accel_desired⟧ + β`.

The horizontal part of `get_thrust_vector` is `accel_target` (`thrust_vector.z = -g`). The
`β`s enter `w` through the rows of `tick` (`course_tube`).

**M4, the attitude contract (the interface this milestone assumes).** Let `aₖ` be the mean
horizontal acceleration of the plant over `[k, k+1]`, per axis in NED. It must equal
`âₖ + ηₖ`, where `â` is the lag law `â_{k+1} = âₖ + αL (c_{k-3} - âₖ)` driven by the commands
`c = accel_target`.

* The constants `αL = 13/500` and `dL = 3` are parameters. A different pair changes `Ah` and is
  absorbed by rerunning `gen_cert.py`, `gen_traj.py`, `gen_lean.py` and `gen_checks.py`.
* The deviation `η` enters the plant rows as `w = (h²/2, h, 0, …) η`.

What `η` must satisfy is the open point:

* In the flight, `|η| ≤ 0.26 m/s²` (rms 0.07), but its effect on the position error is 6.5 mm,
  because `η` is structured: it is driven by the yaw turns at the corners.
* The ℓ1 gain from `η` to `e` is 0.183 m per m/s² (Python: 0.1825 over 16000 ticks, V-tail
  0.002). A sup bound `|η| ≤ 0.26` would therefore give a 4.8 cm tube. That is too wide for T4
  (allowance 15.9 mm, `corner_transfer`), and fits T1 only without the vertical peak
  (`0.0285 + 0.048 = 0.077`).
* The one-step residual of the lag law (`w` on the `a` row) is at most 0.009 per tick, with an ℓ1
  gain of 7.0 m per unit: 6 cm, no better.

So the attitude contract should either:

1. include the heading coupling explicitly (the cross-axis term of the yaw rate times the tilt
   lag, a deterministic function of the nominal heading profile), leaving a small `η`; or
2. provide `η` as the response of a certified linear system to the heading channel, so that its
   effect is computed like the reference response rather than bounded by ℓ1.

The gains in this section are from Python; certifying an ℓ1 gain costs one more trajectory of
about 16000 ticks (about 90 s of kernel time).

**Plant (TRACK_PLAN.md 3.7).** The horizontal rows of the sharp step:

* `p_{k+1} = p_k + h v_k + h²/2 aₖ + ρ`;
* `v_{k+1} = v_k + h aₖ + ρ`.

Here `aₖ` is the mean specific force over the period (horizontal, NED), and `ρ` is the plant
remainder.

**M7/M8, the reference.** The theorems need the navigator's target per axis as the course table
`refN`, `refE`, indexed by S-curve time from the start of leg 1:

* `pos_T(k) = table(τ_k) + ε` with `|ε| ≤ 1 mm` for `corner_transfer`. Through `errResp_add`
  (vertical) or the linearity of `traj`, a deviation of the forcing goes into `w`.
* The blend starts move with the time warp. §3.3 measures their effect: below 0.5 mm. A proof
  needs either the exact blend tick under the warp or a family statement over blend offsets; the
  table fixes the ideal-time rule.
* The time warp itself (`_track_dt_scalar`, `vel_dt_scalar`) is the pacing nominal of M8. It enters
  as the index map `k ↦ τ_k` and the defects `d₁, d₂` of the warped target.

**Not covered here.**

* leg 0 and the corner starts (the horizontal part of the climb, `V(ξ 0)` at the start of leg 1);
* the heading channel and its coupling (above);
* the region `D` itself;
* the pacing nominal;
* the hold at `w₇` (T5b) and T4 at `w₀ = w₇`.

## 8. Files and scripts

**Lean.** All in `contracts/Contracts/Track/`:

* `Horizontal.lean`: constants, `Ah`, `Bh`, `tick`, `tick_eq`, `HAbs`, `absTick`, `errOf_absTick`,
  `forceOf`, `errResp`, `errResp_eq_code`, `errOf_traj_dist`.
* `HorizontalCertData.lean`, generated by `gen_cert.py`: `Ph`, `λ_h`, `γ`, `Psumh` and the
  factorizations.
* `HorizontalCert.lean`: the kernel identities, `Ph_posDef`, `V_A`, `sq_e_le`, `V_iss`,
  `V_traj_le`, `e_traj_le`, `e_traj_le_const`.
* `HorizontalData.lean`, generated by `gen_lean.py`: `DAh`, `Ahat`, `inpH`, the row functions,
  `stepRows_spec`, `stepH`, `v12eq`, `trajOK`.
* `HorizontalTrajN.lean`, `HorizontalTrajE.lean`, generated by `gen_lean.py`: the chunk lists and
  their transition checks.
* `HorizontalChecks.lean`, generated by `gen_checks.py`: the norm, corner, end and tail checks.
* `HorizontalCourse.lean`: `ent_step`, `step_real`, `rounding_bound`, `resp_close`, `resp_tail`,
  `course_norm`, `course_N`, `course_E`, `corner_vehicle`, `corner_transfer`, `course_tube`.

**Python.** In
`/private/tmp/claude-501/-Users-ryan-Research-delegate/547e050f-c29a-418f-816a-16412bc752a6/scratchpad/horiz6/`,
run with the venv of `../vert5/.venv`:

* `ctrlcheck.py`: the controller law against `thr_n`, `thr_e`;
* `fitlag.py`, `closedloop.py`, `cl2.py`, `clrot.py`, `val2.py`: the attitude interface fit;
* `hexact.py`: the rational `Ah`, `Bh`, row by row as in Lean;
* `scurve.py`: the legs (`calculate_path`, `add_segments`, `get_jerk_accel_vel_pos_at_time`);
* `course.py`: the course with the blend rule;
* `warpcmp.py`, `warpcmp2.py`: validation against `vsp`/`asp`;
* `blendpert.py`: the sensitivity to blend offsets;
* `nominal.py`, `lyap.py`, `l1.py`: the nominal response, the certificate exploration and the
  gains;
* `gen_cert.py`, `gen_traj.py`, `gen_lean.py`, `gen_checks.py`: the generators.

Regenerate with `gen_cert.py`, then `gen_traj.py`, then `gen_lean.py` and `gen_checks.py`.
