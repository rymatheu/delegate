# The vertical channel (milestone M5, discrete-time part)

This note documents `Contracts/Track/Vertical*.lean` (library `Track`), the M5 milestone of
TRACK_PLAN.md: the real-valued linear model of the vertical loop, its Lyapunov certificate and
discrete ISS bound, its ℓ1 gain, and the certified error response to the S-curve climb. The
connection to the float code (the C-series lemmas) is not part of this milestone. Section 7 states
the interface it needs.

Everything is sorry-free. `#print axioms` shows only `propext`, `Classical.choice` and
`Quot.sound` (AxiomCheck.lean, end of file). The kernel checks use `decide +kernel`, not
`native_decide`.

## 0. Results

| quantity | value | Lean |
|---|---|---|
| model vs. recorded flight (`lean-course-1ms`) | max \|Δez\| 3.2 mm over 7797 ticks, 2.5 mm in the climb (ticks < 1500), rms 1.3 mm | Python, §2 |
| spectral radius of `A_v` | 0.997436 (time constant 0.98 s) | |
| contraction factor | `λ_v = 0.998` | `V_A` |
| Lyapunov matrix | `P_v` symmetric positive definite (8×8, integers, cond 1.5·10⁵) | `Pv_posDef`, `certV` |
| output weight | `ez² ≤ γ V`, `γ = 5.547·10⁻¹¹` | `sq_ez_le` |
| ℓ1 gain, `\|a_z\| ≤ 1 m/s²` | `\|ez\| ≤ 0.1161 m` at every tick | `l1_gain` |
| S-curve climb, `L ∈ [0.5, 0.8] m`, any start phase | **`\|ez\| ≤ 0.0875 m`** at every tick | `scurve_climb` |
| same, for every bang-bang profile of the family | `\|ez\| ≤ 0.0875 m` | `bang_bound`, `bang_bound_L` |
| kernel time | 55 s for `VerticalData.lean` (44 s of it kernel), 4–8 s for each of the other files | §6 |

The target was 0.095 m. The certified bound of 0.0875 m leaves 7.5 mm for the tube (float error,
plant remainder, tilt coupling, pacing defects).

## 1. The model (`Vertical.lean`)

**State.** The state is `ξ = (ez, ev, eV, eA, I, f, u, w)`, all deviations from hover trim:

| # | state | code variable |
|---|---|---|
| 0 | `ez = z - sp` | plant `p.z` against `_pos_target_ned_m.z` (NED, down) |
| 1 | `ev = vz - vsp` | plant `v.z` against `_vel_desired_ned_ms.z` |
| 2 | `eV` | `ps._pid_vel_d_m._error` (velocity error filter, 5 Hz) |
| 3 | `eA` | `ps._pid_accel_d_m._error` (acceleration error filter, 20 Hz) |
| 4 | `I` | `ps._pid_accel_d_m._integrator` minus its trim value |
| 5 | `f` | `ms._throttle_filter.output - 1/2.25` (2 Hz filter) |
| 6 | `u` | `ms._throttle_in - 1/2.25` (set by `set_throttle_out`, read by the next `motors.output`) |
| 7 | `w` | mean held actuator minus `1/2.25` (plant `held`, read by the sample's specific force) |

**Tick.** `tick` follows the order of `Vehicle.tick` (TRACK_PLAN.md 3.1), one statement per `let`:

1. `update_throttle_filter`: `act = f + αT (u - f)`;
2. `AC_P_1D` (linear zone) and `AC_PID_Basic`: `eV' = eV + αV ((-kpPos ez - ev) - eV)`;
3. `AC_PID` (acceleration): `eA' = eA + αA ((kpVel eV' + asp) + amax w - eA)`, then
   `I' = I + kiDt eA'`;
4. `set_throttle_out`: `u' = -(kpAcc eA' + I')`;
5. the plant (exact double integrator, ZOH): `ez' = ez + h ev + h²/2 (-amax act - asp) - d₁` and
   `ev' = ev + h (-amax act - asp) - d₂`, with `f' = w' = act`.

Here `d₁ = sp' - sp - h vsp - h²/2 asp` and `d₂ = vsp' - vsp - h asp` are the defects of the
target sequence. They are zero when the target is an exact double integral of a piecewise-constant
acceleration.

**Theorems.** `tick_eq` proves `tick ξ a d₁ d₂ = A_v ξ + a B_v - d₁ e₀ - d₂ e₁`.
`errOf_absTick` proves that the tick written in the code's own variables (`VAbs`, `absTick`)
becomes `tick` after the change to error coordinates. `errResp_eq_code` lifts this to whole runs.

**Constants.** They are exact rationals, taken as the float32 values the code computes:

* `αV = 4886901/2²⁶`, `αA = 16042859/2²⁶`, `αT = 16352567/2²⁹`. These are
  `calc_lowpass_alpha_dt(2500·1e-6f, fc)` evaluated in float32, with `fc = 5, 20, 2`;
* `kpPos = 1`, `kpVel = 5`;
* `kpAcc = 0.05f`;
* `kiDt = 0.1f · 0.0025f` (exact product);
* `h = 1/400` (`per_eq`: `Contracts.Plant.h`);
* `amax = 2.25 · 9.80665` (`amax_eq`: `Contracts.Plant.amax`).

The parameters are those of `copter-cf2x*.txt`: PSC_D_POS_P 1, PSC_D_VEL_P 5 (I = D = FF = 0),
PSC_D_ACC_P 0.05, I 0.1, D = FF = 0, FLTT 0, FLTE 20, SMAX = PDMX = 0, MOT_THST_HOVER 0.4444.
The trim offsets (`0.4444f` against `1/2.25`, `9.80665016f` against `g`) shift the integrator's
equilibrium and are absorbed into the deviation `I`.

Numerically:

```
A_v =  1        0.0025    0        0         0     -6.68528e-05 -2.10024e-06  0
       0        1         0        0         0     -0.0534822   -0.00168019   0
      -0.0728205 -0.0728205 0.92718 0         0      0            0            0
      -0.0870413 -0.0870413 1.10824 0.760943  0      0            0            5.27479
      -2.17603e-05 -2.17603e-05 2.77061e-04 1.90236e-04 1  0       0            0.0013187
       0        0         0        0         0      0.969541     0.030459     0
       0.00437383 0.00437383 -0.0556893 -0.0382374 -1 0          0           -0.265058
       0        0         0        0         0      0.969541     0.030459     0
B_v = (-3.125e-06, -0.0025, 0, 0.239057, 5.97643e-05, 0, -0.0120126, 0)
eig A_v = 0.997436, 0.996249 ± 0.005353 i, 0.955632, 0.899795, 0.812302, 0, 0
```

The two zero eigenvalues come from redundant states: after one tick, `f = w`, and `u` is a function
of `(eA, I)`. They are kept because `held` and `_throttle_in` are separate variables in the code
and in the plant.

## 2. Validation against `sim/out/lean-course-1ms/flight.csv`

The script is
`/private/tmp/claude-501/-Users-ryan-Research-delegate/547e050f-c29a-418f-816a-16412bc752a6/scratchpad/vert5/validate2.py`.
It uses the same rational `A_v`, `B_v` as Lean (from `exact.py`). The recorded target
`(sp_d, vsp_d, asp_d)` drives the model, together with its defects, from the recorded initial
error.

| | flight | model |
|---|---|---|
| max \|ez\| | 0.0848 m (tick 890) | 0.0859 m |
| ez at ticks 300, 600, 800, 882, 1000, 1200 | -0.0060, -0.0275, -0.0755, -0.0846, -0.0671, -0.0076 | -0.0059, -0.0274, -0.0771, -0.0859, -0.0667, -0.0066 |
| max \|Δez\| | 3.2 mm (tick 3018, a corner of the course) | |
| max \|Δez\|, ticks < 1500 | 2.5 mm | |
| rms \|Δez\| | 1.3 mm | |

A variant that adds the tilt coupling (cos of the actual tilt against the angle boost of the target
tilt) does not reduce the residual (3.9 mm), so the residual is left to the tube.

## 3. The Lyapunov certificate (`VerticalCertData.lean`, `VerticalCert.lean`)

**Construction.** `P_v` solves the Stein equation `(A/0.9978)ᵀ P (A/0.9978) - P = -I`, scaled so
that `max P_ij = 10¹²`, and rounded to integers. `λ_v = 499/500`. Let
`M = λ_v² P_v - A_vᵀ P_v A_v`. Its exact `L D Lᵀ` factorization (`Lc`, `Dc`, rationals with up to
about 1200 bits) is computed in Python's `fractions` by `gen_cert.py`.

**Kernel checks.** Each identity below is one `decide +kernel` on `Matrix (Fin 8) (Fin 8) ℚ`, and
each takes a few seconds:

* `certV`: `λ² Pv - Avᵀ Pv Av = Lc · diag Dc · Lcᵀ`, with `Dc_nonneg` (min `Dc` = 6.8·10⁶);
* `certP`: `Pv = Lp · diag Dp · Lpᵀ`, with `Dp_pos`, and `Lp_mul_inv` (`Lp` is invertible). From
  these, `Pv_posDef`;
* `certO`: `γ Pv - e₀e₀ᵀ = Lo · diag Do · Loᵀ`, with `Do_nonneg`;
* `Pv_symm_Q` and `Psum_eq` (`Σ|P_ij|`).

**Real-valued theorems.**

* `V_A`: `V(A x) ≤ λ² V x`.
* `V_iss`: `V(A x + w) ≤ λ V x + V w/(1-λ)`. This is Young's inequality `qf_add_le` with
  `η = (1-λ)/λ`.
* `comparison`: the discrete comparison lemma. If `V(k+1) ≤ μ V k + c k`, then
  `V n ≤ μⁿ V 0 + Σ_{k<n} μ^(n-1-k) c k`. `comparison_const` is the constant-input version.
* `V_traj_le` and `ez_traj_le`: for every trajectory `x(k+1) = A_v x k + w k` with
  `V(w k) ≤ c k`, the vertical position error satisfies
  `|ez n| ≤ √(γ (λⁿ V(x 0) + Σ λ^(n-1-k) c k/(1-λ)))`.
* `ez_traj_le_const` is the constant-disturbance version.
* `tube_bound`: nominal response plus tube.

A remark on use. `P_v` is badly conditioned with respect to `ez` (cond 1.5·10⁵, `γ` small against
the large entries of `P`). The certificate is therefore used for tails, rounding and contraction.
It is not used for the reference response: the gain bound through the certificate,
`√(γ BᵀPB)/(1-λ)`, is about 3.6 m per m/s².

## 4. The ℓ1 gain (`VerticalClimb.lean`, `l1_gain`)

Statement: for every target acceleration sequence with `|a k| ≤ 1` (exact reference, from rest),
`|ez n| ≤ 0.1161 m` at every tick.

The bound is `Σ_j |g_j|`, where `g_j = e₀ᵀ A^j B` (`G_eq_pow`), split into two parts:

* the first 3000 terms: computed from the certified step response (`l1_head`),
  `≤ 0.115965 + 6·10⁻⁹`;
* the tail beyond tick 3000: `≤ 2.1·10⁻⁷/(1-λ) = 1.05·10⁻⁴` (`G_tail`, through `V` and `tailG_check`).

Python gives 0.11602. This reproduces the plan's finding 3: the worst-case gain alone cannot prove
δ = 0.095.

## 5. The S-curve climb (`VerticalClimb.lean`, `VerticalSCurve.lean`)

### 5.1 What `SCurve` generates for a vertical leg

`SCurve::calculate_track` → `add_segments(L)` → `calculate_path(Sm, Jm, 0, Am, Vm, L/2)`. The
configured limits give:

* `Jm = WP_JERK = 5` (`ATC_RATE_*_MAX = 0`, so the angular-rate bound is unused);
* snap `Sm = Jm π/(2 max(ATC_INPUT_TC, 0.1)) / 2 = 39.27`;
* `Am = WP_ACC_Z = 1`;
* `Vm = WP_SPD_UP = 2.5` (never reached).

From these, `tj = Jm π/(2 Sm) = 0.2 s`, and `|At| = Jm tj`, so the `else` branch applies with
`t2 = Am/Jm - tj = 0`, `t6 = 0` and `t4 = (√(1 + 25 L) - 3)/5`. The acceleration ramp therefore
consists of the increasing-jerk segment (`Jm/2 (1 - cos(π t/tj))`) and the decreasing-jerk segment.
Its jerk is the raised-cosine pulse `5/2 (1 - cos 5πu)` on `[0, 0.4]`, which integrates to
`Am = 1`. The cruise segment `t15` is zero.

So the target acceleration is the pulse convolved with the bang-bang profile: `+1` on `[0, T₁)`,
`-1` on `[T₁ + 0.4, 2T₁ + 0.4)`, with `T₁ = 0.4 + t4` (`T1ofL`). For `L ∈ [0.5, 0.8]`,
`T₁ ∈ [0.5348, 0.7165] ⊂ [213/400, 287/400]` (`T1_mem_of_L`).

**Validation of the closed form** (`scurve.py`). The recorded `(vsp_d, asp_d)` were matched against
the closed form `(V(τ), A(τ))` for `L = 0.7865` (the course start), comparing `A` at equal `V`. This
comparison does not depend on the time warp. In the acceleration phase (522 ticks) the difference
is at most 4.8·10⁻⁵ m/s², and the peak speed matches to 10⁻⁷ (0.709135).

The recorded deceleration differs: its peak is 0.83 instead of 1, and it ends at -0.113 m/s
instead of 0. The reason is that the course's leg 0 blends into leg 1 at `w0` (fast waypoint), so
its deceleration is not the stop profile. The recorded start is also time-warped by
`_track_dt_scalar`, which starts at 0.

### 5.2 Statements

**Definitions.** `scurveRef s₀ L k = ∫₀^0.4 pulse u · bangRef (s₀ + u) (T1ofL L) k du`
(componentwise) is the nominal climb from rest, at S-curve time `kh - s₀`. It is the S-curve of
§5.1: the convolution commutes with integration in time. `bangRef s T₁ k` is the bang-bang profile
with its switching times at `s, s + T₁, s + T₁ + 0.4, s + 2T₁ + 0.4`. These are arbitrary reals,
not tick-aligned. The profile is sampled with its exact position and velocity.

**Theorems.**

* `scurve_climb`: for all `s₀ ≥ 0`, `L ∈ [1/2, 4/5]` and ticks `k`,
  `|errResp (scurveRef s₀ L) k 0| ≤ 0.0875`.
* `bang_bound` and `bang_bound_L`: the same bound for every bang-bang member.
* `scurve_bound`: the same bound for every average of bang-bang members over any probability
  measure of start times.
* `errResp_weighted_bound`: the general averaging lemma.
* `errResp_add`: superposition.

### 5.3 How the bound is computed

1. **Superposition with real switching times** (`errResp_stepRef`). Take a unit acceleration step
   at real time `s`, with `J = ⌈s/h⌉` and phase `ψ = J - s/h ∈ [0, 1)`. Its response is
   `XA(k-J) + ψ XV(k-J) + ψ² XP(k-J)`, where:
   * `XA` is the response to the tick-aligned step;
   * `XV` is the free response to a reference velocity jump of `h`;
   * `XP` is the free response to a reference position jump of `h²/2`.

   `forceOf_stepRef` computes the defects at the switch.
2. **Patterns.** The four switch ticks have gaps `G₁ = J₁ - J₀ ∈ [⌊T₁/h⌋, ⌈T₁/h⌉] ⊂ [213, 287]`,
   `J₂ - J₁ = 160` exactly, and `G₃ ∈ [⌊T₁/h⌋, ⌈T₁/h⌉]`, so `|G₁ - G₃| ≤ 1` (`Jof_gap`,
   `Jof_add_gap`). That leaves 75 × 3 = 223 integer patterns.
3. **Certified step response.** The integer trajectory `trajA` is the floor-rounded recurrence with
   scale `2⁴⁴·5⁴`, over 3001 ticks. Every transition is checked in the kernel. The rounding error
   is a disturbance below `1/Sz` per tick and is absorbed by `V_iss` (`rounding_bound`): the stored
   and true `ez` differ by at most 10⁻¹² (`XA_close`). The same holds for `XV` over 801 ticks.
4. **Pattern sums**, checked in the kernel for all 223 patterns and ticks `k < 1736` (`pat_all`):
   `|E(k) - E(k-G₁) - E(k-G₁-160) + E(k-G₁-160-G₃)| ≤ 0.08485`. After tick 1736 every term is at
   least 1000 ticks past its switch, and `|XA m 0| ≤ 0.014` for `m ≥ 1000` (`XA_tail`, through
   `V(XA 1000 - X∞)` and the exact steady state `X∞ = (0, 0, 0, 0, 1/amax, -1/amax, -1/amax, -1/amax)`).
   This gives `|pattern| ≤ 0.0849 = BA` (`sumA_bound`).
5. **Phase terms.** `|XV| ≤ 0.00064` (`XV_bound`: data up to tick 800, then the `V` tail) and
   `|XP| ≤ 10⁻⁵` (`XP_bound`, from the `V` of its start). Each of the four switches contributes at
   most `ψ·0.00064 + ψ²·10⁻⁵`.
6. **Total.** `Bbang = 0.0849 + 4·0.00064 + 4·0.00001 = 0.0875`.
7. **Averaging.** The raised-cosine pulse is a probability density (`integral_pulse`), so the
   S-curve response is the pulse-weighted average of bang-bang responses
   (`errResp_integral`, `errResp_weighted_bound`).

### 5.4 Numbers (Python, same model)

| L (m) | ideal S-curve peak | bang-bang peak (tick-aligned) |
|---|---|---|
| 0.5 | 0.0644 | 0.0658 |
| 0.6 | 0.0719 | 0.0734 |
| 0.7 | 0.0779 | 0.0797 |
| 0.7865 (course) | 0.0822 | 0.0841 |
| 0.8 | 0.0827 | 0.0847 |

For comparison, at the course start: the recorded error is 0.0848, the model driven by the
recorded target gives 0.0859, and the certified bound is 0.0875.

The 2 mm by which the flight exceeds the ideal S-curve comes from the time warp at the leg start
and from the corner blend at `w0`. The certified bound is the bang-bang maximum plus 2.6 mm for
the sub-tick phases.

## 6. Kernel time (risk E5 / R13)

The file is built with `lake build`; times were measured by `-Dprofiler=true`.

| file | build | content |
|---|---|---|
| `Vertical.lean` | 4.2 s | model, generic lemmas |
| `VerticalCertData.lean` | 2.7 s | rational matrices |
| `VerticalCert.lean` | 4.4 s | the 8 kernel identities (each < 2 s) and the real-valued corollaries |
| `VerticalData.lean` | **55 s**, 44 s of it kernel | 119 trajectory chunks (3801 transitions, 14 s, about 3.7 ms per 8-state transition with 130-bit coefficients); 75 pattern theorems (223 × 1736 four-term sums, 29 s, about 75 µs per sum); ℓ1 and tails 1.5 s |
| `VerticalClimb.lean` | 8.2 s | soundness of the checks, ℓ1, bang-bang family |
| `VerticalSCurve.lean` | 4.0 s | S-curve, averaging, tube |

**Lessons for the plan.** These measured costs shape how the certificates should be written:

1. **Kernel-friendly data.** Trajectories are best stored as `List (ℕ × … × ℕ)` literals, with an
   offset encoding and a raised `maxRecDepth`. `List ℤ` literals elaborate a hundred times slower.
   A single big `Nat` literal is no better, because the kernel's per-access cost is linear in the
   literal's size.
2. **Loop structure.** Loops are best driven by a fuel `ℕ` with structural recursion. A
   `List`-structural `brecOn` loop, or a `List.range` loop, is quadratic in the kernel.
3. **Split the checks.** Checks should be split into many small theorems (chunks of 32
   transitions). One long `decide` degrades superlinearly; 800 transitions took 19 s in one
   theorem against 4.3 s in 25 chunks.
4. **Linearity instead of cells.** The plan's 40 × 20 cell cover with one certified nominal per
   cell is unnecessary for V. One step response and the pattern sums cover the continuum of `L`
   and of start phases.

**Extrapolation to H (32 real states).** A transition costs about 16 times more, roughly 60 ms. A
certified free or step response over 3000 ticks would then take about 3 min, which is feasible if
the same superposition replaces the cells. Per-cell nominals (8·10⁵ cell-ticks) would not be
feasible: about 16 h.

## 7. Interface to the controller lemmas (C-series) and to the S-curve library (M7)

**What the theorems need.** The theorems are about the real model. To join them to the float
code, the following facts are needed at every tick `k ≥ 2` on the region `D` (TRACK_PLAN.md 3.2,
D6, D8, D13). Write `⟦·⟧` for the real value of a float, `β` for an explicit bound and `w` for the
`World`. The C-series forms are "output = ideal law + β".

**C1, `update_estimates`.**
`⟦ps._pos_estimate_ned_m.z⟧ = z_k + β`, `⟦ps._vel_estimate_ned_ms.z⟧ = vz_k + β`. Here `z_k`,
`vz_k` are the sampled plant values.

**C5, `AC_P_1D.update_all` then `AC_PID_Basic.update_all_float3_bool2`.** Preconditions: the
filter is not in reset, the limits are off, and `|error| ≤ linear_dist` (D6). Then:

* `⟦vt⟧ = kpPos (⟦pos_target.z⟧ - ⟦pos_est.z⟧) + ⟦_vel_desired.z⟧ + β`;
* `⟦eV⁺⟧ = ⟦eV⟧ + αV ((⟦vt⟧ - ⟦vel_est.z⟧) - ⟦eV⟧) + β`;
* `⟦_accel_target.z⟧ = kpVel ⟦eV⁺⟧ + ⟦_accel_desired.z⟧ + β`.

The gain scaler is `1`, the offsets are `0` and the terrain term is `0`.

**C6, `AC_PID.update_all` (acceleration).** Preconditions: `FLTT = 0`, `SMAX = 0` (so
`Dmod = 1`), `PDMX = 0`, no reset, `limit = false`, and `|I| < IMAX` (D13). Then:

* `⟦eA⁺⟧ = ⟦eA⟧ + αA ((⟦at⟧ - ⟦am⟧) - ⟦eA⟧) + β`, with
  `⟦am⟧ = ⟦sample.accel_ef.z⟧ + ⟦9.80665016f⟧`;
* `⟦I⁺⟧ = ⟦I⟧ + kiDt ⟦eA⁺⟧ + β`;
* `thrust_d_norm = kpAcc ⟦eA⁺⟧ + ⟦I⁺⟧ - ⟦0.4444f⟧ + β`.

**C7, `set_throttle_out(-thrust_d_norm, true, 2)`.**
`⟦ms._throttle_in⟧ = (⟦0.4444f⟧ - kpAcc ⟦eA⁺⟧ - ⟦I⁺⟧) / ⟦cos_roll cos_pitch⟧ + β`, the angle boost.
Also, the filter cutoff is 2 Hz.

**C12, `AP_MotorsMatrix.output`.** Preconditions: armed, no throttle limits, `thr_adj` interior
(D8). Then `⟦_throttle_filter.output⁺⟧ = ⟦f⟧ + αT (⟦_throttle_in⟧ - ⟦f⟧) + β`, and the mean of
the four actuators equals `⟦_throttle_filter.output⁺⟧ + β`. The QUAD-X roll, pitch and yaw factors
sum to zero.

**Plant (TRACK_PLAN.md 3.7).** The vertical rows of the sharp step are

* `z_{k+1} = z_k + h vz_k + h²/2 (g - amax · mean(act_k) · R₃₃) + ρ`;
* `vz_{k+1} = vz_k + h (g - amax · mean(act_k) · R₃₃) + ρ`;
* the sample's `accel_ef.z = -amax · mean(held_k) · R₃₃ + ρ`.

The second-order terms `ρ` are explicit.

**From these to the model.** With these facts, the code's tick in error coordinates is
`ξ_{k+1} = A_v ξ_k + forceOf r k + w_k`, where `r k` is the navigator's target triple and `w_k`
collects:

* the `β`s, mapped through the rows of the tick: `w_k = E β_k` with `E` read off `tick`;
* the tilt coupling `amax · act · (1 - R₃₃/cos θ_T)` and `(R₃₃ - 1)` terms;
* the trim offsets: `0.4444f - 1/2.25` and `9.80665016f - g` enter as a constant input that the
  integrator absorbs, so include them in `w` or shift `I`.

`tube_bound` then gives
`|ez k| ≤ |errResp r k 0| + √(γ c)/(1 - λ)` whenever `V(w_k) ≤ c`, and `V_le_of_abs_le` gives
`V(w) ≤ Psum · ε²` from `|w_i| ≤ ε`.

That route is crude because of the conditioning of `P_v`. For a componentwise-small `w`, a tighter
tube comes from the impulse responses of the individual `w`-channels (as `l1_gain`): their kernel
cost is one more certified trajectory each.

**M7 interface.** The theorems need the navigator's target as an explicit sequence:

* `r k = scurveRef s₀ L k + ε_k` on leg 0 (from rest, vertical, `L = |w0 - p|`), with
  `errResp_add` splitting off `errResp ε`. With an ideal time base (`τ_{k+1} = τ_k + h`), this is
  the statement "`SCurve.get_jerk_accel_vel_pos_at_time` = the closed form of §5.1". The float
  `powf`/`sinf` evaluation contributes `ε` of order 10⁻⁶.
* The time warp of `_track_dt_scalar` and `vel_dt_scalar` at the leg start, and the corner blend
  into leg 1, are **not** small (TRACK_PLAN.md 3.5.1). They must enter either as a modified nominal
  (the pacing dynamics) or through `errResp ε` with ε bounded by a certified response, not by ISS.
* In the recorded flight they move the peak from 0.0827 (ideal) to 0.0848.

**Not covered here.** The following belong to M4, M6 or M8 and to the tube:

* the horizontal and heading channels;
* the tilt coupling;
* the region `D` itself (the linear zone of `sqrt_controller`, inactive limits);
* ticks 0 and 1 (`reset_filter`);
* the pacing nominal.

## 8. Files and scripts

**Lean.** All in `contracts/Contracts/Track/`:

* `Vertical.lean`: model, change of coordinates, `traj`, quadratic forms, Young inequality, ISS
  step, comparison lemma.
* `VerticalCertData.lean`, generated by `gen_cert.py`: `Pv`, `λ`, `γ` and the factorizations.
* `VerticalCert.lean`: kernel checks of the certificate, `V_A`, `Pv_posDef`, `sq_ez_le`,
  `V_traj_le`, `ez_traj_le`.
* `VerticalData.lean`, generated by `gen_data.py`: `trajA`, `trajV`, transition chunks, patterns,
  ℓ1 and tail checks.
* `VerticalClimb.lean`: from the checks to the real responses, `l1_gain`, `errResp_eq_code`,
  `errResp_stepRef`, `bang_bound`, `T1_mem_of_L`, `errResp_integral`, `scurve_bound`.
* `VerticalSCurve.lean`: `pulse`, `integral_pulse`, `scurveRef`, `scurve_climb`, `errResp_add`,
  `tube_bound`.

**Python.** In
`/private/tmp/claude-501/-Users-ryan-Research-delegate/547e050f-c29a-418f-816a-16412bc752a6/scratchpad/vert5/`,
with a venv holding numpy, scipy and sympy:

* `consts.py`: float32 constants;
* `exact.py`: the rational `A_v`, `B_v`;
* `validate2.py`: comparison with the flight;
* `lyap.py`, `gen_cert.py`: the certificate;
* `vnums.py`: bound ingredients;
* `gen_data.py`: the data file;
* `scurve.py`: the closed form against the recorded target;
* `smooth.py`, `family.py`: S-curve and bang-bang peaks.

## 9. The leg-0 escape (`pace_esc`, INDUCTION.md): analysis, not yet certified

**Request.** Certify that the S-curve time `q` reaches `τ_v` (218–226 ticks) by tick `W₀ = 350`
from the start of leg 0. The scaler filter has `α = 1118481/2²⁷`, and the raw scaler is the
along-track formula of PACING.md.

**Status.** By the coordinator's decision, `pace_esc` enters the main theorem as the explicit named hypothesis `ClimbEscape`. This section records why it is not discharged and the route to discharge it later. No Lean file is added. Every cheap certificate fails, with the numbers below. The route
that works numerically needs a tighter early tube than the induction's `Inv` provides.

**Coupled model** (`esc.py`). The coupled model is A_v and B_v in error coordinates, driven by the
S-curve sampled at the warped time `q·h`. The raw scaler at tick `k+1` is
`clamp(0.05 + (v_z - 1.5 (sp_k - z_{k+1}))/|v_T|, 0, 1)`, with `|v_T| = V(q_k h)`, and it equals 1
while `|v_T|² < 2⁻²³`. Then come the filter and the progress `q ← q + s`.

* Escape tick of the model: 287 for `L ∈ [0.6, 0.8]` and 288 for `L = 0.5`. The measured escape
  is 280–291 (PACING.md §4; vertical legs 290–291, tilted legs 280–285).
* The q-trajectory matches the nominal flight: `q(101) = 86.9` against 86.0 measured, and
  `q(281) = 219.3` against 217.9.
* `L` matters only once `q > T₁ ≥ 213.9` ticks.

The physical escape is very robust. The model's escape tick under perturbations:

| perturbation | escape tick |
|---|---|
| none | 287 |
| initial deviation `±10⁻⁴` in `I`, `f`, `u` or `w` | 288–291 |
| constant bias of the numerator, `±10⁻⁴` | 288–291 |
| constant bias `-10⁻³` | 295 |
| constant bias `-5·10⁻³` | 304 |

**What fails.**

1. **Interval bands on `(s, q)`** with worst-case vehicle lag over the band (`band.py`). The
   decorrelation between the lag and `|v_T|` blows the band up: `q(350) ∈ [141, 339]`.
2. **Comparison with the unwarped climb.**
   * At equal tick: the raw scaler is not lower (min difference -0.002), but the lower bound gives
     only `q(350) ≥ 219.6 < 224`.
   * At equal S-curve time (`warp2.py`): this holds empirically for every filtered warp, with a
     margin of at least 0.011. But the monotone 2-D lower bound gives only `q(350) ≥ 189`.

   The escape depends on the feedback itself. A slowed target with an unscaled velocity
   feed-forward puts the vehicle ahead, and that raises the raw scaler above the unwarped value.
3. **A structural sign argument also fails.** The kernels of `ev + 1.5 ez` to the defect pushes
   are nonnegative only up to lag 297 (e₀) and 307 (e₁). The acceleration-step lag is not
   monotone: its minimum is at lag 185.
4. **Plain Lipschitz deviation bounds** explode (`sens.py`): `Dq(350) ≈ 214`. The cause is the
   factor `1/|v_T|` at the start, where `|v_T| ≈ 3.5·10⁻⁴` when the formula switches on.

**What works numerically** (`refined.py`). This is a deviation analysis along a computed nominal.
It splits the deviation of the q-history into a uniform shift, whose effect on the raw scaler is
the nominal's derivative `κ_k` with `|κ_k| ≤ 0.004` per tick of `q`, and increments bounded by the
history of `|δs|`. The latter enter through the ℓ1 sums of the kernels of `ev + 1.5 ez`. A
second-order remainder is added. Result: `|δq(350)| ≤ 0.55` ticks for a numerator perturbation
`|η| ≤ 10⁻⁶`, and `≤ 6.3` ticks for `|η| ≤ 10⁻⁵`. Both certify escape by tick ≤ 295. For
`|η| = 10⁻⁴` the bound reaches 108 ticks and fails.

**Obstruction.** The induction's own bounds give a tube on `ev + 1.5 ez` over the first 350 ticks
of about `6·10⁻⁴`. The two main parts are:

* `ε0V` at tick 2 (`10⁻⁴` on `I`, `f`, `u`, `w`, through a peak gain of 3.1): `4·10⁻⁴`;
* `εV` per tick (the integrator row `2·10⁻⁷` through an ℓ1 gain of 801): `2·10⁻⁴`.

This is 30 to 60 times what a perturbation argument tolerates while `|v_T| < 10⁻³`. The global
radii `τV` are larger still (6.3 mm/s on `ev`).

**Proposed route.** These are the ingredients of a certified `pace_esc`:

* **C16 tighter at the start.** The takeover holds hover, so the initial deviation should be
  near float level, about `10⁻⁶`. Alternatively, keep the start spread as an explicit family.
* **A magnitude-aware finite-horizon tube for ticks ≤ 350.** In the climb's first 350 ticks
  `|I| ≤ 0.05`, so the integrator `β` is about `10⁻⁹` per tick, not `2·10⁻⁷`.
* **An M7 interface on the target.** The target should be stated as an explicit rational
  surrogate `Γ̃(q)` of the S-curve, within about `10⁻⁷`.
* **This file's machinery for the coupled nominal**, extended in three ways:
  * an exact fixed-point nominal of the coupled map, with division and clamp;
  * `κ_k` from a derivative trajectory, together with the kernel sums;
  * the bound recursion `(Dq, Ds)`, checked in the kernel.
* **The deviation lemma** in Lean: the uniform-shift and increment split, second-order bounds of
  `Γ̃`, the division and the clamp.
* **Tilted legs.** The along-track numerator is `cos²θ` times the V ratio plus `sin²θ` times the
  H ratio. The same machinery applies with A_h, but the comparison between V and H is not
  monotone in the warp, so the H channel has to be carried along.

The estimated effort is several days of Lean (about 1.5–3k lines), and a kernel time of minutes.
The scripts are in
`/private/tmp/claude-501/-Users-ryan-Research-delegate/547e050f-c29a-418f-816a-16412bc752a6/scratchpad/vert5/`
(`esc.py`, `warp.py`, `warp2.py`, `warp3.py`, `band.py`, `sens.py`, `refined.py`).
