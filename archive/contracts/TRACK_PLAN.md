# Proof plan for `track_contract`

This is a plan, not a proof. It covers the open theorem

```lean
theorem track_contract (sense32 senseP w₀) (hM : MissionWorld w₀)
    (hS : Plant.CopterSense sense32 senseP) (hL : LibmSpec) :
    Mloop sense32 senseP w₀ ⊨ ⟨Atakeoff, lang_t 0 ψtrack⟩
```

of `Contracts/Mission/Sub.lean`. It takes into account the spec change of 2026-11-05: `Atakeoff`
now admits any initial heading `ψ₀ ∈ (-π, π]` (level, at rest, in the box, hover held).

Section 0 summarizes the plan. Sections 1–2 cover the statement and the evidence. Section 3 is the
mathematical argument, including the yaw transient (3.8). Section 4 lists the controller lemmas,
Section 5 the pacing, Section 6 the Lean structure, Section 7 the risks, Section 8 the effort and
milestones, and Section 9 the experiments to run before any Lean work.

---

## 0. Summary

**What has to be shown.** At every tick up to 12000, for every closed-loop behavior from the
takeoff assumption:

* (T1) the tracking error is at most `δ = 0.095`;
* (T2) the rigid body stays in an envelope;
* (T3) the error is at most `δ₀ = 0.035` during the climb out of the box;
* (T4) near each waypoint, the vehicle is within `r = 0.1` whenever the target is within
  `rPass = 0.105`.

In addition (T5), the target reaches `w0 … w7` in order within the allowances and then holds near
`w7`.

**Findings that shape the plan.** All were measured in this session from
`sim/out/lean-course-1ms/flight.csv`, with the scripts in the scratchpad (Section 9).

1. **The 8.7 cm maximum error is vertical.** It occurs at tick 882, at the end of the climb to `w0`.
   The vertical error peaks at 8.48 cm and the horizontal error never exceeds 3.0 cm. The vertical
   loop is sluggish for two reasons:
   * the throttle passes through a 2 Hz low-pass filter (`set_throttle_out(…, 2.0)`, then
     `AP_MotorsMulticopter::update_throttle_filter`);
   * the gains are the defaults `PSC_D_ACC_P 0.05`, `PSC_D_ACC_I 0.1`, `PSC_D_VEL_P 5`.

   The slowest closed-loop mode has a time constant of about 1 s.
2. **The vertical channel is linear in flight.** An 8-state linear model built from the translated
   code (P on position, then the velocity PID with its 5 Hz error filter, the acceleration PID with
   its 20 Hz error filter and integrator, the 2 Hz throttle filter, the one-tick delays and an exact
   vertical double integrator) reproduces the flight's vertical error within **3.2 mm** at every
   tick of the run. No limiter, saturation or nonlinearity acts in the vertical channel during the
   flight.
3. **A worst-case gain bound cannot prove `δ = 0.095`.** The ℓ1 norm of the impulse response from
   vertical target acceleration to vertical error is **0.116 m per m/s²**. With the course's
   vertical acceleration limit of 1 m/s², the best input-class-free bound is 0.116 m, which is above
   `δ`. Through the jerk channel (5 m/s³) the bound is 0.45 m.

   The real error, 0.086 m, is the response to the particular S-curve. A jerk-limited climb profile
   reproduces 0.0862 m for the 0.8 m climb. Shorter climbs give smaller peaks:

   | climb | peak vertical error |
   |---|---|
   | 0.5 m | 0.067 m |
   | 0.6 m | 0.075 m |
   | 0.7 m | 0.081 m |
   | 0.8 m | 0.086 m |

   **So T1 is plausibly true for the whole box, with about 9 mm of margin. It can only be proved
   with a reference-specific computation, not with an ISS gain.**
4. **T4 is directional.** At the corners `w1 … w6`, the target is within 0.105 for 31–33 ticks. In
   that window the error is up to 3.5 cm, yet the vehicle is within 0.0765–0.0792 m of the waypoint,
   so T4 holds with **1.85–2.35 cm of margin**. The reason is that the vehicle understeers toward the
   apex. An isotropic error bound would give `0.105 + 0.035 > 0.1`. T4 therefore needs the *signed*
   error along the nominal trajectory, from a tube around a computed nominal. At `w0 = w7` the margin
   is 1.85 cm, during the climb overshoot.
5. **The pacing is a closed-loop property.** The target's S-curve time advances at the filtered
   rate `track_dt_scalar ∈ [0, 1]`. This rate depends on the measured velocity and position error.
   The velocity and acceleration feedforward are *not* rescaled by it, so while it is below 1 the
   target triple (position, velocity, acceleration) is inconsistent. That inconsistency is an input
   to the error dynamics.
6. **The plant's sup-norm Grönwall bound cannot be used per tick.** `norm_traj_sub_le` takes `Klip`
   on a ball whose radius includes the position (‖x‖ ≥ 2.5 m), which gives `K ≈ 1400`. The Euler
   constants are translation invariant but about 70 times loose in the velocity rows: the
   equivalent acceleration error is 0.84 m/s² at `W = 1`. Through the gain of finding 3 that is about
   0.1 m of position error. A new **block-wise one-step lemma** is needed: a Grönwall bound on the
   `(q, ω)` subsystem only, plus explicit integration of the `(p, v)` rows (3.7).

**Architecture.** I recommend **"nominal plus contraction tube"** in three layers:

* **(a) Linear-regime normal form.** On a region `D`, one tick of the translated controller equals
  a real affine law up to a float error `β` (Section 4). The plant step equals its exact ZOH
  linearization up to a second-order remainder (3.7).
* **(b) Contraction certificate.** Quadratic Lyapunov matrices per channel are checked by
  reflection in the kernel. They give ISS and ℓ1 bounds for the *small* inputs: float error,
  nonlinear remainders, yaw coupling, start-state spread and pacing defects.
* **(c) Certified nominal.** The *large* part is the response of the linear(ized) loop to the
  S-curve family. It is computed in interval arithmetic and checked by a reflection checker in the
  kernel (no `native_decide`). It supplies the signed, phase-resolved errors that T1, T3, T4 and the
  hold need.

A pure Lyapunov/ISS route proves T2 and the hold. It can prove T1 only with a relaxed `δ`. For that
case there is a hedge: `δ` enters the assembly only through `ρ + δ ≤ 0.25` and `δs`, and
`hδ : δ < r` is not used. Since `nav_contract`'s `ρ` was measured at 0.071, the decomposition can be
rebalanced to `δ' ≈ 0.14`, `ρ' ≈ 0.11` without touching the mission. The pure route does not prove
T4.

**Effort.** About **56–88 person-weeks** (13–20 person-months) for an expert working with agents,
with an estimated 60–70 % chance that all current constants survive unchanged. There are nine
milestones, each a sorry-free theorem of independent interest (Section 8). The S-curve semantics
(about 10 weeks) is shared with `nav_contract`.

---

## 1. The statement, decoded

`ψtrack = □_[0,12000](errLE δ ∧ envF ∧ takeoffF ∧ proxAllF) ∧ reachSeqT rPass legs ∧ ◇_[0,10800] □_[0,1200] nearT w7 rPass`.

| part | content | depends on |
|---|---|---|
| T1 | `dist (pos x_t) (posTarget x_t) ≤ 0.095` | tracking |
| T2 | `|p_i| ≤ 10`, `|v_i| ≤ 2`, `|ω_i| ≤ 10` | follows from region `D` |
| T3 | `inColumn(target) ∧ polyDist(target) > 0.155 → err ≤ 0.035` | early climb, corner starts only |
| T4 | for each `w ∈ {w0 … w7}`: `‖target − w‖ ≤ 0.105 → ‖pos − w‖ ≤ 0.1` | signed tracking near corners |
| T5a | `reachSeqT 0.105 legs`: the target is within 0.105 of `wᵢ` in order, each within `Tᵢ` ticks of the previous one | S-curve geometry (corner cut ≤ 0.1006) and pacing |
| T5b | `◇_[0,10800] □_[0,1200] ‖target − w7‖ ≤ 0.105` | end of leg 7 and the loiter target |

Signal alignment. `posTarget x_t` is `_pos_desired_ned_m` *after* tick `t`, which consumed the
sample of `x_t`. `pos x_t` is the plant state at tick `t`. `err` therefore compares the state with
the target computed from it, as `flight.csv` does.

**The heading change.** `startState` will need `q = (cos(ψ₀/2), 0, 0, sin(ψ₀/2))`. I assume
`Atakeoff` becomes `∃ p ψ₀, inBox p ∧ (x 0).phys = startP p ψ₀`. Every plan lemma below takes `ψ₀`
as a parameter. `tickSpecForce` is unchanged: the hover thrust along body-down of a level vehicle
is still `(0, 0, −g)`.

`w0 = w7 = (0, 0, −0.8)`, so T4 at `w0` and at `w7` are the same atom. Its window spans both the
climb overshoot (from tick 711) and the final hold.

---

## 2. Evidence

### 2.1 Measured, nominal run (`lean-course-1ms`: start (0, 0, −0.0135), heading 0)

| quantity | value | comment |
|---|---|---|
| max err | 0.0870 m (tick 882) | vertical 0.0848; horizontal max 0.0300 |
| err in the last 400 ticks | ≤ 0.0137 m | hold phase |
| actuators | 0.3995–0.4853 | never saturating; spread between motors ≤ 0.028 |
| max tilt | 16.2° (roll 14.8°, pitch 11.5°) | `ATC_ANGLE_MAX 30` |
| max |roll − roll target|, |pitch − pitch target| | 0.71°, 0.62° | attitude loop tight |
| max |p − p_t|, |q − q_t| | 0.18, 0.15 rad/s | rate loop |
| max |ω| | p 1.04, q 0.81, r 1.17 rad/s | r from the 90° yaw turns at the corners |
| max |v| | 0.82 per axis (speed 1.10) m/s | |
| max target accel | NE 2.12, D 1.0 m/s² | `WP_ACC 1.5`, `WP_ACC_Z 1`, corners; jerk 5 |
| thrust vector NE (accel command) | ≤ 2.92 m/s² | lean limit `g·tan 30° = 5.66` |
| T4 margins at w1…w6 | 2.16, 2.35, 2.27, 2.30, 2.08, 2.08 cm | windows of 31–33 ticks; err ≤ 3.5 cm in them |
| T4 margin at w0/w7 | 1.85 cm | window from tick 711, err ≤ 7.2 cm |
| closest target approach w1…w6 | 0.10002–0.10056 m | 4.4 mm below `rPass` |
| track scaler | 0 at every leg start, < 0.8 on 418 ticks | MISSION.md |

### 2.2 Monte Carlo (`montecarlo`, `-worst-case`, `-ref-2000`)

* 2212 starts, all with heading 0. Every mission verdict holds.
* Leg times: leg 0 1.36–1.70 s, leg 1 1.92–2.08 s, the other legs identical to 10 ms. Slack is at
  least 0.92 s (leg 1).
* The hold best-window distance is 2.81 cm in every run. After leg 1 the trajectories are the same
  up to a time shift. This is direct evidence of incremental contraction.
* `montecarlo-freefall` (tick-0 specific force 0 instead of `−g`) misses leg 0's allowance in 78 of
  200 runs (leg 0 up to 3.61 s). **Pacing is sensitive to the initial controller state.** The Lean
  assumption fixes the hover reading (`tickSpecForce_startP`), so this case is excluded, but it
  shows that the leg-0 margin is not robust to start-up transients.

### 2.3 What the evidence does *not* cover (to be generated, Section 9)

* **Per-tick tracking error over the Monte Carlo.** The run files store position, yaw and actuators
  only, not the target. T1 and T3 at corner starts are unmeasured.
* **Arbitrary initial heading.** No run has `ψ₀ ≠ 0`.
* **The model being proved.** The data comes from PyBullet: semi-implicit, 1200 Hz substeps, ground
  contact for 14 of 200 starts, a backward-difference specific force. The theorem is about the exact
  flow of `vf` with the instantaneous specific force and no ground. The differences are small but
  unquantified, and the constants should be revalidated on a model-faithful simulator.

---

## 3. The mathematical argument

### 3.1 State, tick order and delays

**Plant state.** `x_t ∈ ℝ¹³` (p, v, q, ω) and `held_t` (the actuators of the period that ended at
`t`).

**Controller state on the path.** These are the hidden `World` fields that matter. Everything else
(logs, counters, PWM outputs) is carried along but does not feed back.

| block | states |
|---|---|
| position NE (`AC_P_2D`, `AC_PID_2D`) | PID_2D error filter (5 Hz), derivative filter (5 Hz) and `error_last`, integrator (`kimax 10`); `_pos_desired`, `_vel_desired`, `_accel_desired` (written by the navigator) |
| position D (`AC_P_1D`, `AC_PID_Basic`, `AC_PID`) | velocity error filter (5 Hz); acceleration error filter (20 Hz), integrator (`kimax 0.8`); slew limiter (inert: `SMAX = 0`, early return) |
| motors | `_throttle_in`, throttle filter (2 Hz), `limit.*` flags, the actuators |
| attitude | `_attitude_target` (quaternion), `_ang_vel_target`, `_ang_accel_target` (input shaping, `ATC_INPUT_TC 0.05`), `_thrust_angle`, `_thrust_error_angle`, `_ang_vel_body` (the rate target for the next tick), `_althold_lean_angle_max` (filtered) |
| rate PIDs (`AC_PID`, three axes) | target filter (20 Hz), error filter (yaw only, 2.5 Hz), derivative filter (20 Hz), integrator (`IMAX 0.5`) |
| navigator | S-curve legs (this/prev/next), S-curve time, `_track_dt_scalar` (filter, `tc = WP_ACC/WP_JERK = 0.3 s`), `_offset_vel/accel` (speed ramp), flags, mission index, yaw mode |

**Tick order** (`Vehicle.tick`). The sample is `s_t = sense(x_t, held_t)`.

1. `rate_controller_run`: the gyro of `s_t` against the rate targets that tick `t − 1` set.
2. `motors.output`: the throttle filter runs on `_throttle_in` of tick `t − 1`, then the mixer
   produces `act_t`.
3. The AHRS view reads `s_t`, then `update_estimates(s_t)`.
4. `auto_run`: mission update, then `update_wpnav` (target advance from `s_t`), then
   `NE_update_controller`, then `D_update_controller`, then `set_throttle_out`, then
   `input_thrust_vector_heading` (with `s_t`'s quaternion), which sets the rate targets for tick
   `t + 1`.
5. The plant moves: `x_{t+1} = Φ_h(x_t, act_t)` and `held_{t+1} = act_t`.

**Latencies.** The outer loops (position, attitude, throttle) act through `s_t → act_{t+1} → x_{t+2}`,
a two-tick latency of one computation delay plus the ZOH. The rate loop acts through
`s_t → act_t → x_{t+1}`, one tick. The specific force in `s_t` reflects `act_{t−1}`. Each delay is one
extra state, the previous command, in the closed-loop vector `ξ`. The 8-state vertical model of
finding 2 contains exactly these delays.

### 3.2 The region `D` (linear regime)

`D` is a set of `(x, held, World)` on which every branch on the path takes its *nominal* side,
every sqrt controller is in its linear zone, and every limiter is inactive. The thresholds below
are proposals. They leave margin over the nominal values and are to be finalized after experiment
E1. `D` is used in its strict form `D°`, with each bound tightened by a margin `m`, so that the
induction closes (3.6).

| # | condition | proposed bound | nominal | what it switches off |
|---|---|---|---|---|
| D1 | `‖q‖ = 1` | exact (`Mplant_qnormSq`) | — | — |
| D2 | thrust angle (tilt) | ≤ 22° | 16.2° | `limit_accel_xy`, lean limit, `althold` limit (acos(0.444/0.8) = 56°), angle boost clamp |
| D3 | `|ω_x|, |ω_y|` | ≤ 2 rad/s | 1.04 | plant constants; rate PID linearity |
| D4 | `|ω_z|` | ≤ 1.4 rad/s | 1.17 | covers the yaw slew `ATC_RATE_WPY_MAX 60°/s = 1.047` plus the turn-rate feedforward |
| D5 | `|v|` | ≤ 1.5 m/s | 1.10 | T2; the stopping-point linear zone |
| D6 | position error `|e|` (NE, D) | ≤ δ and inside `linear_dist = D1_max/kp²` of each P stage | ≤ 0.087 | `sqrt_controller` linear branch; `AC_P_*` `error_max` inactive (the target is not pulled toward the vehicle) |
| D7 | `|accel_target_NE|` | ≤ 4 m/s² | 2.92 | `limit_accel_xy` (5.66), `_limit_vector` reset |
| D8 | `_throttle_in`, throttle filter, all `act_i` | ∈ [0.30, 0.62] | 0.40–0.49 | throttle limits, `rpy_scale = 1`, `thr_adj` interior, every `limit.*` flag false, `set_actuator_with_slew` clamps inactive |
| D9 | `|roll_in|, |pitch_in|` | ≤ 0.1 | spread ≤ 0.028 | mixer headroom |
| D10 | `|yaw_in|` | ≤ `yaw_allowed` (≥ 0.2) | small | `limit.yaw` false (or tolerated: it only gates the yaw integrator) |
| D11 | thrust error angle | ≤ 30° | about 0.7° | full feedforward branch of `attitude_controller_run_quat` |
| D12 | roll/pitch angular acceleration targets | ≤ `ATC_ACC_R/P_MAX` = 31.4 rad/s² | ≤ 10 | `attitude_command_model` roll/pitch linear |
| D13 | rate integrators < 0.5; acceleration-D integrator < 0.8; NE integrator < 10 | strict | small | integrator clamps inactive |
| D14 | heading-channel state: see 3.8 | — | — | the yaw branches are *modeled*, not excluded |
| D15 | all floats finite, magnitudes inside the ports' ranges | ports: f32 ≤ 100, f64 ≤ 10⁴ | — | NaN/Inf guards (`is_nan`, `isFinite`) never fire |
| D16 | `cos_roll · cos_pitch ≥ 0.1` | implied by D2 | — | angle-boost `inverted_factor = 1` |
| D17 | navigator in a normal leg state | mission index, S-curve segment indices in range | — | no reinit; the `fast_waypoint` logic is the intended one |

### 3.3 Linear-regime normal form and channel split

On `D`, Section 4 gives

  `ξ_{t+1} = A ξ_t + B r_t + w_t`,

where:

* `ξ` stacks the deviations of the states of 3.1 from trim (hover thrust `1/2.25`, level);
* `r_t` is the reference triple from the navigator (position, velocity, acceleration);
* `w_t` collects
  * the float error `β`,
  * the plant remainder (3.7),
  * the nonlinear terms (second order in tilt, rates and yaw coupling),
  * the trim offset `MOT_THST_HOVER 0.4444` against `1/2.25 = 0.44444…`.

At linear order around level hover with heading `ψ`, `A` splits into three channels. Their
couplings are second order and go into `w`:

* **vertical (V)**: 8 states (z, v_z, the velocity and acceleration error filters, the
  acceleration integrator, the throttle filter, `_throttle_in` delay, `held` delay). Validated to
  3.2 mm (finding 2).
* **horizontal (H)**: about 16 states per axis, written as one complex 16-vector (north + i·east).
  They are: position and velocity; the PID_2D error and derivative filters, `error_last` and
  integrator; tilt (thrust direction) and tilt rate; the attitude target angle with its shaping
  velocity and acceleration; the rate PID target filter, derivative filter and integrator; the
  rate-target delay and `held`.

  The complex form is exact at linear order because the position controller and
  `attitude_from_thrust_vector` are rotation-equivariant in NED. The body-frame rate states are
  rotated by `ψ`, which 3.8 handles.
* **heading (Y)**: about 8 states (ψ, r, the attitude target yaw with its shaping velocity and
  acceleration, the yaw rate PID target and error filters and integrator, `held`). The yaw shaping
  is *saturating* (slew 1.047 rad/s, acceleration 4.71 rad/s²) during large heading changes, so Y
  is treated as a nonlinear but bounded subsystem (3.8).

The second-order couplings are:

* V gets `(1 − cos tilt)`, offset by angle boost to the error between `cos(target tilt)` and the
  actual `cos_roll·cos_pitch`;
* H gets `g·(tan − sin)` terms and the thrust magnitude times the tilt error;
* Y feeds H through frame rotation and the gyroscopic term `(Jz − Jy)/Jx · q r` (`gyro = 0.55`).

### 3.4 Contracting measure

For each channel `c ∈ {V, H, Y_lin}`, a rational symmetric `P_c ≻ 0` and `λ_c < 1` with
`A_cᵀ P_c A_c ≼ λ_c² P_c` are computed numerically (Section 9, E2) and **checked in Lean** by an
exact `L D Lᵀ` certificate of `λ_c² P_c − A_cᵀ P_c A_c` (Section 6.4). For the complex channel H,
`P_H` is Hermitian, or equivalently a real 32×32 matrix commuting with the rotation `J ⊗ I`. That
form makes `V_H` invariant under rotations of the NED frame.

The joint measure is the weighted maximum `V(ξ) = max_c μ_c ‖ξ_c‖_{P_c}`. The cross-couplings are
second order on `D`, so they pass a small-gain test with explicit margin.

`λ_V` is set by the slowest vertical mode (a time constant of about 1 s, so `λ_V ≈ 0.9975` per
tick). `λ_H` and `λ_Y` are faster. `V` is used three ways:

1. **ISS for the small inputs.** `V(ξ_{t+1} − ξ̂_{t+1}) ≤ λ V(ξ_t − ξ̂_t) + ‖w_t − ŵ_t‖_*`, with `ξ̂`
   the certified nominal. This is a discrete comparison lemma (6.3). The tube radius is then
   `ρ_tube(t) ≤ κ(λ^t ρ₀ + Σ λ^{t−1−k} β̄)`, where `κ = cond(P)^{1/2}` converts back to coordinates.
2. **Tails of ℓ1 gains.** `Σ_{k≥N} ‖C A^k B‖ ≤ ‖C‖ κ λ^N/(1 − λ) ‖B‖`.
3. **The hold** (3.11): after the target stops, `V` of the error contracts geometrically.

### 3.5 Two layers: reference response and tube

Finding 3 rules out a single ISS bound with the reference as input. The error is split as

  `ξ_t = ξ̂_t + η_t`,

where `ξ̂` is the **certified nominal**: the solution of the real affine model (3.3) with `w = 0`,
driven by the *ideal S-curve* reference, from the nominal start. `η` is the tube. Then:

* `ξ̂` is computed in interval arithmetic (dyadic intervals with outward rounding) and checked tick
  by tick by a reflection checker. It gives the signed errors, so T4 can be decided per tick from
  it.
* `η` is driven by
  * `w` (float error, remainders),
  * the yaw coupling (3.8),
  * the pacing defect (3.5.1),
  * the start-state spread (3.5.2),

  and bounded by 3.4(1).

Both layers are needed only while the reference is "large", that is during leg 0 and the corners.
Everywhere else the crude ISS bound is enough.

**3.5.1 The reference and its defect.** The navigator writes `(pos_T, vel_T, acc_T)`. Write `τ` for
the S-curve time and `S(τ)` for the ideal S-curve. Section 5 bounds the time-warp
`τ_{t+1} = τ_t + h · s_t`, with `s_t = _track_dt_scalar · vel_dt_scalar ∈ [0, 1]`. Then:

* `pos_T(t) = S(τ_t)` up to float error;
* `vel_T = S'(τ_t)·vel_dt_scalar`;
* `acc_T = S''(τ_t)·vel_dt_scalar² + offset accel`.

When `s_t < 1`, `vel_T` is not the derivative of `pos_T`. The defect `(1 − s_t)·S'(τ_t)` enters `w` as
a velocity-feedforward error. It is **not small**: up to 0.2 m/s on the 418 ticks where `s < 0.8`. So
the nominal `ξ̂` must contain the scaler dynamics. The scaler is part of the nominal model (a
1-state filter driven by along-track error and velocity), not of the tube. This makes the nominal
loop *nonlinear* through the clamp and the division by `|vel_T|`. The certified simulation handles
that directly, because interval arithmetic does not need linearity.

**3.5.2 The start-state family.** The start is `p ∈ box` (3 parameters) and `ψ₀` (1 parameter).

* `ψ₀` enters only the heading channel and, through it, the H inputs (3.8). It is treated as a
  disturbance and not parametrized.
* `p` changes leg 0: the target runs straight from the stopping point `≈ p` to `w0`. On `D`, the leg-0
  reference is `p + u(p) σ(τ; L(p))`, with `L = |w0 − p| ∈ [0.5, 0.835]` and `u` the unit direction.
  The S-curve profile `σ(·; L)` is a scalar function of `L`. At linear order the response splits
  into the V and H responses to `σ` weighted by `u`.

  So the nominal family has two parameters, `L` and the angle of `u` from the vertical. Cover them
  with cells (for example 40 × 20). Each cell runs its own certified nominal over leg 0 and the
  `w0` corner (about 1200 ticks). The spread inside a cell goes into the tube through a Lipschitz
  bound in `(L, angle)`.
* **Merging.** After leg 0 the reference is the same S-curve for every start: from `w0` on the
  legs are fixed, and the time warp only shifts time. The state at the "leg-1 start" event of each
  cell lies in a common small set, shown by contraction. One nominal, indexed by S-curve time from
  that event, covers legs 1–7 and the hold. The Monte Carlo shows exactly this: identical leg
  times and hold distances from leg 2 on.

### 3.6 The invariant and the induction

Define `Inv t` to hold when all of the following hold:

1. `(x_t, held_t, World_t) ∈ D°`, the strict region;
2. `η_t ∈ Tube(t)` in the measure `V`;
3. the navigator's phase indicators match the nominal's within the time-shift bound (Section 5).

**Base case.** `Inv 0` follows from `Atakeoff` and `MissionWorld`: the takeover relaxes the
attitude controller, resets the throttle filter to hover, and initializes the PID filters with
their `reset_filter` flags. Ticks 0 and 1 take special branches (`first_tick`,
`_reset_filter`). They are proved separately by direct evaluation from the start state, with `p`
and `ψ₀` symbolic.

**Step.** `Inv t → Inv (t+1)`:

* on `D°`, Section 4 makes the controller step equal the affine law up to `β`;
* 3.7 makes the plant step equal its ZOH linearization up to `ε_pl`;
* the nominal checker certifies `ξ̂_{t+1}` and that `ξ̂_{t+1} ⊕ Tube(t+1) ⊆ D°` holds with margin `m`;
* the ISS lemma gives `η_{t+1} ∈ Tube(t+1)`.

The margin `m` is what turns "inside `D` at `t`" into "inside `D` at `t + 1`" without a continuity
argument. Because the induction is over the 12001 ticks of the horizon, no unbounded-time
statement is needed.

**No actuator saturation** is part of `D°` (D8). It follows because the certified actuators are
`0.4444 + (V, H, Y responses)` with a tube of a few 10⁻³. Nominal: 0.3995–0.4853 against the bounds
[0.30, 0.62].

### 3.7 The plant step: where Grönwall replaces the Euler algebra

**Why the existing bounds fail** (finding 6):

* `norm_traj_sub_le` uses `Klip (box ‖x‖)` on the sup norm of the whole 13-vector, so the position
  enters the Lipschitz radius;
* `step_sub_eulerStep_le` is translation invariant, but its velocity-row constant uses `amax` and
  the crude `Mq`, and is about 70 times the true size.

**New lemma (P4, `Contracts/Plant/Sharp.lean`).** Let `y = (q, ω) ∈ ℝ⁷`. Its field `f_y(y, u)` does
not depend on `(p, v)`. On `‖ω‖_∞ ≤ W` and `‖q‖ = 1` its Lipschitz constant is
`K_y = O(1 + W + gyro·W)`, about 3 for `W = 2` (no position term). Use Mathlib's
`dist_le_of_approx_trajectories_ODE` (or `norm_le_gronwallBound_of_norm_deriv_right_le`) on `y`
alone, against the explicit curve `ŷ(t) = (q₀ ⊗ exp(t ω₀/2) + O(t²α), ω₀ + t α₀)` with
`α₀ = J⁻¹(τ(u) − ω₀ × Jω₀)`. This gives

  `|q(t) − q̂(t)| ≤ c_q t²`, `|ω(t) − ω̂(t)| ≤ c_ω t²`,

with `c_q, c_ω` depending only on `W` and the torque bound on `D` (the motor spread ≤ 0.1 bounds
`|α| ≤ 2·596·0.1`).

The `(p, v)` rows are then integrated explicitly. The thrust magnitude `a(u)` is constant over the
period, so

  `v(h) = v₀ + h g e_z − a(u) ∫₀ʰ d(q(t)) dt`.

`d(q(t)) = d(q₀) + t·Dd(q₀)[q̇₀] + O(t²)` follows from the `q` bound, giving

  `v(h) = v₀ + h(g e_z − a d(q₀)) − a (h²/2) Dd(q₀)[q̇₀] + r_v`, with `|r_v| ≤ a h³/6 · C(W, α)`,

and `p(h)` follows likewise at `O(h⁴)`.

**Size.** `a ≈ 10` and `C(W, α) ≈ W² + |α|` give, on `D`, `|r_v| ≲ 2·10⁻⁵` m/s per tick. That is an
equivalent acceleration error of about 0.008 m/s², or under 1 mm through the 0.116 gain. The
linear model of 3.3 uses the exact `h²/2` term, which is the exact ZOH discretization of the
linearization. The remaining nonlinearity (`d(q)` quadratic in tilt) goes into `w`.

This lemma is where the exact flow pays off. The p and v rows are an exact quadrature of the
solution. The Grönwall bound is applied only to the 7-dimensional attitude block, which has a small
Lipschitz constant. The `step_unique` and `traj_hasDerivAt` theorems already in `Flow.lean`
provide the curve.

### 3.8 The yaw transient (new: arbitrary initial heading)

**Where heading enters.** The coupling is weaker than it first looks. In each function below,
heading and tilt are handled separately:

* `AC_PosControl::get_thrust_vector` returns `(accel_NE, −g)` in NED. It does not depend on
  heading. Auto mode drives the attitude through `input_thrust_vector_heading`. The lean angles
  computed by `accel_NE_mss_to_lean_angles_rad` (which uses `atanf`, `cos_yaw`, `sin_yaw`) are
  stored but not used on this path.
* `attitude_from_thrust_vector(tv, ψ_cmd)` composes the thrust rotation, about an NED-horizontal
  axis, with the heading rotation. So the commanded tilt is the same for every `ψ_cmd`.
* `thrust_heading_rotation_angles` first splits the error into the thrust-vector correction
  (`thrust_vector_rotation_angles`) and then the heading error. The heading error is clipped to
  `heading_error_max = min(inv_sqrt_controller(1/ATC_RAT_YAW_P, ATC_ANG_YAW_P, accel), 45°) = 45°`.
  When the clip is active, the attitude target is reset to `body ⊗ thrust_correction ⊗ heading
  step`. The tilt error that the angle controller sees does not depend on the size of the heading
  error.
* In `input_thrust_vector_heading_rad`, `attitude_command_model` shapes the three axes
  independently. On yaw it saturates at the slew `get_slew_yaw_max_rads = ATC_RATE_WPY_MAX = 60°/s`
  (`ATC_RATE_Y_MAX = 0`) and at `ATC_ACC_Y_MAX = 270°/s²`.
* `get_throttle_boosted` uses `cos(thrust angle)` and `cos_roll · cos_pitch`, the `R₃₃` element,
  which does not depend on heading. The vertical channel is heading-free.
* The mixer `output_armed_stabilizing` handles yaw last and with the lowest priority. Its allowance
  is computed against `min(0.5, throttle_avg_max)`, with a floor of `MOT_YAW_HEADROOM · 0.001 = 0.2`.
  Yaw saturation sets `limit.yaw`, which only gates the yaw integrator. Roll, pitch and throttle are
  untouched while `rpy_scale = 1` (D8, D9).

**Where heading does couple** (all second order, entering H as inputs):

1. **Frame rotation of the body-frame rate-loop states.** The target filters, derivative filters,
   integrators and the rate-target delay live in the body frame. In NED-complex form they rotate by
   `e^{−iΔψ}` per tick. The coupling input is `|r| h · |ζ_fast|`, where `ζ_fast` is the vector of
   body-frame fast states. They are small on `D`: rate errors ≤ 0.2 rad/s, integrators near 0
   because the vehicle has no torque bias.
2. **The gyroscopic term** `(Jz − Jy)/Jx · q r`: at most `0.55 · 2 · 1.4 ≈ 1.5` rad/s². That is
   0.25 % of the roll authority (596 rad/s² per unit roll input).
3. **Feedforward projection.** `ang_vel_body_feedforward = (body⁻¹ ⊗ target) · ang_vel_target`. A
   yaw rate about NED-down has body components `r sin(tilt)` (up to 0.38 rad/s at 22°). This is
   correct kinematics, and the plant's `q̇ = ½ q ⊗ ω` matches it. Only the second-order mismatch
   (tilt error × r) enters `w`.
4. **Mixer.** The yaw torque uses motor differential. On `D`, the yaw demand of a slewing turn is
   about `J_z · 4.71 / (2 · kmkf · fmax · 0.5 · 4) ≈ 0.014` (yaw input units), far below 0.2.

**When the transient happens.** The yaw command comes from `AC_PosControl::calculate_yaw_and_rate_yaw`:

* yaw target = the bearing of the horizontal desired velocity when that speed exceeds
  `0.05 · vel_max = 0.05` m/s;
* otherwise, the current attitude-target yaw.

Consequences:

* **Starts near the axis** (`|p_NE| ≲ 0.04` m). The leg-0 velocity is almost vertical, the target
  yaw stays at `ψ₀`, and there is no turn on leg 0.
* **Off-axis starts.** During leg 0 the horizontal target speed crosses 0.05 m/s, and the yaw
  target jumps to the bearing toward the axis, a step of up to π. It jumps back to "hold" when the
  speed drops below 0.05 near `w0`. The command steps, but the shaped attitude target slews at
  ≤ 1.047 rad/s.
* **Leg 1.** The yaw target becomes 45° (the direction `w0 → w1`). The turn is up to π, which takes
  about 3 s at the slew. That is longer than leg 1 (about 2 s), so **the heading transient overlaps
  the whole of leg 1, the `w1` corner (T4) and part of leg 2.** In the nominal run (`ψ₀ = 0`) the
  turns are at most 90°, each about 1.5 s.

**Effect on the tracking statements.**

* **δ (T1).** Dominated by the vertical channel, which is heading-free at linear order. The H
  inputs from (1)–(3), passed through the H ℓ1 gain (to be computed in E2; expect about 0.05 m per
  m/s² by analogy), add an estimated 1–3 mm. Not critical (margin about 9 mm), but it has to be
  measured (E4).
* **δ₀ (T3).** Active only for corner-ish starts in the first ~27 % of the leg-0 path, which is
  exactly when an off-axis start turns toward the axis. The vertical error there is ≤ 0.012 m in
  the nominal run. With about 2 cm of margin to 0.035 (and the hard geometric cap 0.0364), a few mm
  of yaw-induced horizontal error is acceptable. Medium risk.
* **T4 at w1 (and w2).** The margin is about 2.2 cm. The tube must absorb the yaw-coupling
  inflation, estimated at a few mm. This is the most yaw-sensitive statement. Recommendation E4:
  Monte Carlo over `ψ₀`, recording the target.
* **Pacing on legs 0–2.** The scaler sees heading only through the position and velocity errors,
  so it is unaffected at first order. Leg 1's slack of 0.92 s is the smallest; E4 must report the
  leg-1 times for `ψ₀ ∈ {±π, ±3π/4, ±π/2}`.

**Extra region conditions on heading (D14).** The invariant does **not** need a bound on the
heading error itself: the clip and the thrust/heading split make the tilt loop independent of it.
It needs:

* (Y1) `|r| ≤ 1.4` rad/s: the slew 1.047 plus the turn-rate feedforward `|a_turn|/|v|`, clamped by
  the shaping, plus the rate-loop overshoot;
* (Y2) the yaw-axis states of `attitude_command_model` (shaped yaw rate ≤ 1.047, shaped acceleration
  ≤ 4.71) and the yaw rate PID integrator `< 0.5`;
* (Y3) `|yaw_in| ≤ yaw_allowed`, or at least the Y subsystem's output inside its bounds even when
  `limit.yaw` fires;
* (Y4) the attitude target's Euler pitch away from ±90°, implied by D2, so that `to_euler` (atan2f,
  asinf) is accurate;
* (Y5) **no reversal near π.** The heading error in `thrust_vector_rotation_angles` is `wrap_PI` of a
  quaternion angle. At exactly π the turn direction is decided by rounding and the sign of `q1`. The
  plan needs a lemma that after the first tick of a step command, the heading error moves away from
  ±π monotonically and never re-crosses it, so that the yaw rate does not chatter. Proof: the shaped
  yaw rate has a fixed sign while `|error| > 45°`, and the error decreases at ≥ 0.9 · 1.047 rad/s
  once the slew is reached.

**The branch cut at the start.** With `ψ₀ = π`, `get_att_target_euler_rad.z` evaluates
`atan2f(±0, −1)`. `LibmSpec.atan2f` gives no accuracy on the branch cut, only the range ±(π + ε).
Both values are the same heading, so the proofs must not depend on which one is returned. The yaw
commands are compared through `wrap_PI` and quaternions, so stating the Y lemmas modulo 2π
suffices. Alternatively, extend `LibmSpec` with the branch-cut values.

**The Y subsystem in the proof.** It is a nonlinear system with a saturating slew. Its contract is
stated directly, as a component lemma:

> From any heading error and any step command, `|r_t| ≤ 1.4`, `|ṙ_t| ≤ 6`, the rate-PID states stay
> bounded, and the error reaches 0 monotonically within `|Δψ|/1.0 + 0.5` s.

It is proved by a phase argument (slew phase, then linear phase with its own Lyapunov certificate),
not by linearization. Its outputs `(r, ζ_fast)` enter H only as bounded inputs.

### 3.9 Climb-out bound δ₀ (T3)

`takeoffF` is active only while the target is in the column **and** `polyDist(target) > 0.155`.
For targets below `w0` that means horizontal distance from the axis > 0.155, which needs
`|p_N|, |p_E|` both ≳ 0.11 (corner starts). The target leaves that region after about 27 % of the
leg-0 path (0.15–0.22 m of travel, about 0.5–0.6 s). By then the vertical error from rest is
≤ 0.01: the finite-horizon response to the start of the S-curve is small because the error builds
up only during the deceleration near `w0`.

The proof uses the cell nominals of 3.5.2. On each cell, the event "target leaves the ρ-region"
has a certified tick bound, and the certified `|ê| + tube ≤ 0.035` up to that tick. The budget is
about 0.01 nominal plus the tube, against 0.035. The geometric cap from `safe_of_parts` is
`δ₀ ≤ 0.25 − 0.2136 = 0.0364`, so `δ₀` cannot be raised.

### 3.10 The transfer property T4

T4 is checked per tick on the certified nominal:

  `‖S(τ̂_t) + ê_t − w‖ ≤ 0.1 − tube(t) − Δ_shift`,

for every tick of the nominal window `{t : ‖S(τ̂_t) − w‖ ≤ 0.105 + Δ_target}`. Here `Δ_target`
covers the possible target positions of the real behavior at the same S-curve time. The real target
equals `S(τ)` up to float error; the time shift is handled by indexing with `τ`.

Nominal margins are 1.85–2.35 cm. The tube needs to stay under about 1 cm, comfortably above the
expected few mm. This is the statement for which the two-layer architecture is indispensable.

### 3.11 The hold at w7 (T5b) via contraction

When the leg-7 S-curve finishes, the target is `w7` (up to float error). Then:

* **If the vehicle never comes within `WP_RADIUS_M`** (the arrival test `reached_destination` for a
  non-fast waypoint), the mission does not complete and the target stays at `w7`. T5b holds.
* **If it does, at tick `t_c`.** `mission_complete → loiter_start` sets a new S-curve from the
  current target (`w7`) to the stopping point `sp = pos + v_NE · t_stop` (NE), with
  `t_stop = inv_sqrt_controller(|v|, kP = 1.5, accel)/|v|`, and the analogous D stopping point.
  The target then moves on the segment `[w7, sp]`, so it stays within `max(0, |sp − w7|)` of `w7` by
  convexity of the ball. It suffices to show

  `|sp − w7| ≤ |pos_{t_c} − w7| + |v_{t_c}|/kP + float ≤ 0.105`.

  That needs **phase-resolved** bounds at `t_c`: in the nominal run `err ≈ 0.014` and `|v| ≈ 0.02`,
  giving 0.028 (measured: 0.028). The global `δ` alone is not enough: `0.095 + 0.2/1.5 > 0.105`.
  The certified nominal and the tube provide the values at `t_c`.

**The window.** The 1200-tick window inside `[0, 10800]` starts at the first such tick, around tick
6600 in the nominal run. That leaves more than 4000 ticks of slack, so a time shift of up to 10 s
is tolerated.

**T4 at w7 during the hold.** The target is ≤ 0.028 + 0.001 from `w7`. From `t_c + 400` on, the
error contracts to ≤ 0.02, at rate `λ_V` (slowest time constant about 1 s), with the
`IsLyapunovOn`-style monotone `V`. The vehicle is then within 0.05 of `w7`. Between `t_c` and
`t_c + 400`, the nominal and tube are used. The loiter continues to tick 12000 with the same
argument (a fixed target, so the tube decays).

---

## 4. Controller-level lemmas

**Form of each lemma.** For a translated function `f` on the path, with real reading `⟦·⟧` of its
float inputs and state on `D_f` (the part of `D` that `f` sees):

```
f_ideal : (∀ inputs/state on D_f) →
  (the nominal branch is taken at every `if`) ∧
  all outputs/new state finite ∧
  |⟦f(·)⟧ − L_f(⟦·⟧)| ≤ β_f   (componentwise, explicit β_f)
```

Here `L_f` is the real affine (or explicit nonlinear) law.

**How each is proved.**

1. Unfold the translated definition (`simp only [f, Id.run, bind, pure]`).
2. Discharge each `if` with comparison lemmas `decide (a < b) = decide (⟦a⟧ < ⟦b⟧)` on finite
   floats (the port has them: `lt_iff_toReal_lt`, `decide_lt_eq`).
3. Replace each `+ − × ÷ sqrt` by `round(⟦a⟧ ∘ ⟦b⟧)`, using the rounding lemmas
   (`|round x − x| ≤ 2⁻²⁴|x| + 2⁻¹⁵⁰`, or `2⁻⁵³` for doubles). The basic float operations are
   *defined* in core v4.36 through `Float32.Model`, so these are provable. The port's
   `delegate-port/FloatModel/{Add,DivSqrt,Bracket,Small,Order}.lean` (about 3000 lines, standard
   axioms only) proves them for the core model on v4.33. PLANT.md notes that they were not carried
   over. They need porting to v4.36 (P1).
4. Use the `LibmSpec` fields for `sinf`, `cosf`, `sqrtf`, `atan2f`, `asinf`, `acosf`, `fmaxf`,
   `fminf`.
5. Collect the error with a generic **float-error tactic**: a `FloatBound` structure (value
   interval, error bound) with propagation lemmas per operation. This is the single most-used tool
   in the project.

**Gaps in `LibmSpec`.**

* `tanf` (`angle_rad_to_accel_mss`, used every tick for `limit_accel_xy`'s `accel_max`) needs
  range and accuracy on `[0, π/4]`.
* `powf(t, 3)` appears 15 times in the S-curve evaluation (`SCurve`). It needs accuracy for an
  integer exponent of 3, or a proof that the translation's `Float32.pow tj 3.0` agrees with a
  rounded cube.
* `expf` appears only in `SlewLimiter.modifier` after the `slew_rate_max ≤ 0 → return 1` exit. A
  lemma shows the exit is taken (`SMAX = 0`), so no hypothesis is needed.
* `atanf` (`accel_mss_to_angle_rad`) feeds only `_roll/_pitch_target_rad`. A lemma shows that
  nothing on the path reads them, so only finiteness is needed, or none.
* `fmodf` appears in `wrap_PI` and `wrap_2PI` (exact, already in `LibmSpec`).

**Cancellation hazards** (the β must be stated on the right quantity):

* `attitude_from_thrust_vector` and `thrust_vector_rotation_angles` compute `acosf(dot)` with
  `dot ≈ 1` near level flight. One ulp of `dot` (6·10⁻⁸) gives `√(2·6·10⁻⁸) ≈ 3.5·10⁻⁴` rad of
  angle error. The axis `cross/|cross|` is ill-conditioned there too. **State β on the rotation
  vector `axis·angle`**, which is well-conditioned, not on angle and axis separately. The induced
  error is about 3.5·10⁻⁴ rad of tilt, or 3.4·10⁻³ m/s² of horizontal acceleration, under 0.5 mm of
  position.
* `NE_update_controller` subtracts doubles (target − estimate) and then converts to float
  (`Vector2p.tofloat`). That is exact enough, but β must be relative to the *difference*, not to
  the 2.5 m positions.
* `limit_accel_xy`, `Vector2f.limit_length`, `normalize`: divisions by lengths that can be near 0
  (`vel_norm` at leg starts). These are branches; `D` must exclude the near-zero ill-conditioned
  side, or the lemma must state the bound for both sides.
* `advance_wp_target_along_track` divides by `|curr_target_vel|` near leg starts. Since the clamp
  is to `[0, 1]`, the *result* is bounded even when the quotient is badly conditioned. State the
  lemma on the clamped output.

### 4.1 Lemma list, with real laws and size estimates

Lines are Lean proof lines, including the float bookkeeping, assuming the P1 tactic exists.

| # | translated function(s) | ideal law on D | β (order) | lines |
|---|---|---|---|---|
| C1 | `AC_PosControl::update_estimates` | `pos_est = ⟦s.pos⟧`, `vel_est = ⟦s.vel⟧` | exact or 2⁻²⁴ | 80 |
| C2 | `AC_P_2D::update_all` + `sqrt_controller_Vector2f_float3` | `vel_T = kP_NE·(pos_T − pos_est)`, no limiting (D6) | 10⁻⁷ m/s | 250 |
| C3 | `AC_PID_2D::update_all…` (+ `update_i`) | `e_f⁺ = e_f + α_E(v_T − v − e_f)`, `d⁺ = d + α_D((e_f⁺ − e_f)/dt − d)`, `I⁺ = I + k_i e_f⁺ dt`, `a = k_p e_f⁺ + I⁺ + k_d d⁺` | 10⁻⁶ m/s² | 350 |
| C4 | `NE_update_controller` (assembly, `limit_accel_xy` inactive, `calculate_yaw_and_rate_yaw`) | `a_NE = C3 + a_des`; yaw target per 3.8 | 10⁻⁶ | 400 |
| C5 | `AC_P_1D::update_all`, `AC_PID_Basic::update_all_float3_bool2` | vertical P and velocity PI with filter | 10⁻⁶ | 300 |
| C6 | `AC_PID::update_all` (acceleration D; slew limiter returns 1), `D_update_controller` | `thr = hover − (k_p e_f + I)`; `limit_vector.z = 0` | 10⁻⁷ | 450 |
| C7 | `AC_AttitudeControl_Multi::set_throttle_out`, `get_throttle_boosted`, `update_althold_lean_angle_max` | `thr_boosted = thr / cos(θ_T)`; `althold ≥ 50°` | 10⁻⁷ (cosf 2⁻²²) | 250 |
| C8 | `get_thrust_vector`, `attitude_from_thrust_vector` | `q_des = q_tilt(a_NE/g) ⊗ q_ψ(ψ_cmd)` | 4·10⁻⁴ rad on the rotation vector | 450 |
| C9 | `input_thrust_vector_heading_rad…`, `attitude_command_model` (three axes), `thrust_vector_rotation_angles`, `body_to_euler_derivative` | input shaping, linear on roll/pitch (D12), saturating model on yaw (3.8) | 10⁻⁵ rad/s | 700 |
| C10 | `attitude_controller_run_quat`, `thrust_heading_rotation_angles`, `update_ang_vel_target_from_att_error`, `ang_vel_limit` (no limit: `_MAX = 0`) | `ω_T = ff + kP_angle · e_att` (sqrt controller linear), heading clip | 10⁻⁵ | 600 |
| C11 | `rate_controller_run(_dt)`, `AC_PID::update_all` × 3 | per axis: target filter, error filter, derivative filter, integrator; `out = k_p e + I + k_d d` (FF 0, PDMX 0, SMAX 0) | 10⁻⁷ | 450 |
| C12 | `AP_MotorsMatrix::output` → `output_armed_stabilizing`, `update_throttle_filter`, `Thrust_Linearization.thrust_to_actuator` (expo 0, spin 0–1, gain 1), `set_actuator_with_slew` (no slew), `output_to_motors` | `act_i = thr_f + r_i·roll + p_i·pitch + y_i·yaw` with QUAD-X factors; `thr_f⁺ = thr_f + α_2Hz(thr_in − thr_f)` | 10⁻⁷ | 600 |
| C13 | `AP_AHRS_View::update` (`rotation_matrix`, `calc_trig`) | `cos_roll·cos_pitch = R₃₃`, `yaw = atan2(R₂₁, R₁₁)` mod 2π | 10⁻⁶ | 300 |
| C14 | navigator `update_wpnav`, `advance_wp_target_along_track`, `SCurve.advance_target_along_track` (the `SCurve` lemmas are shared with nav, 9.x) | `τ⁺ = τ + h s`, `s` per Section 5; `pos_T = S(τ)` | 10⁻⁶ m | 900 (+ S-curve library) |
| C15 | `Vehicle.tick` glue: `withMotors`, `applyPos`, `replayPos`, `afterWP`, `mission_update`, `verify_nav_wp`, `loiter_start` | the composition, with the event logs evaluated in order | — | 600 |
| C16 | takeover and the ticks 0–1 special branches | direct evaluation from `startP p ψ₀` | — | 400 |

Total: about 7000 lines for the controller layer, plus the S-curve library (Section 5, about
2500 lines, shared).

**The two unconditional lemmas** (milestones M1, M2), needing no `D`:

* **M1, actuators.** `set_actuator_with_slew` ends with `constrain_value_line_float input lo hi`
  (`lo = 0`, `hi = 1` without slew), and `constrain_value_line_float` returns `(lo + hi)/2` on NaN.
  So for every `World` whose stored actuators are in `[0, 1]`, every tick's actuators are finite and
  in `[0, 1]`, and the property is invariant. This also needs: the spool state stays
  `THROTTLE_UNLIMITED` (`wp_run` sets it, `boot` sets it); `motor_enabled` has 4 entries; the
  harness reads `_actuator[0..3]!`, whose default 0 is also in range.
* **M2, integrators bounded.** Every PID integrator is clamped after update:
  * `constrain_value_line_float` to ±IMAX in `AC_PID`, `AC_PID_Basic`, `update_i`;
  * `limit_length` to `kimax` in `AC_PID_2D`.

  So `|I| ≤ IMAX` always, with NaN mapped to 0 by the clamp's midpoint. The filters are bounded
  convex combinations whenever their inputs are bounded.

---

## 5. Target pacing (T5a)

**The mechanism** (`advance_wp_target_along_track`). With
`d = vel_T/|vel_T|`, `e = pos_T − pos_est` and `kP = 1.5`:

* `track_dt_scalar = clamp(0.05 + (v·d − kP e·d)/|vel_T|, 0, 1)` when `|vel_T|² > 0`, else 1;
* `_track_dt_scalar ← _track_dt_scalar + (track_dt_scalar − _track_dt_scalar)·(dt/0.3)`;
* `τ ← τ + _track_dt_scalar · vel_dt_scalar · dt`, where `vel_dt_scalar` is the speed-ramp ratio
  `_offset_vel/_wp_desired_speed`, which reaches 1 after the initial ramp.

**Lemma P-1 (progress when tracking).** If `|v − vel_T| ≤ ε_v`, `|e| ≤ ε_e` and `|vel_T| ≥ v_min`,
then `track_dt_scalar ≥ 1.05 − (ε_v + 1.5 ε_e)/v_min`. That is ≥ 1, clamped to 1, whenever
`ε_v + 1.5 ε_e ≤ 0.05 v_min`. On cruise segments (`|vel_T| ≈ 1`) the nominal and tube give
`s = 1` after the 0.3 s filter transient.

**Lemma P-2 (no freeze; self-correction).** If the S-curve time stalls (`s ≈ 0`), the position
target stops but `vel_T` (not rescaled) keeps feeding forward `S'(τ)`. The vehicle therefore moves
ahead along `d`, `e·d` becomes negative, and `track_dt_scalar` returns to 1. As a closed-loop
statement:

> Every interval with `s < 1 − η` has length at most `L_w` (certified from the nominal and tube,
> per leg start).

Since the nominal contains the scaler dynamics (3.5.1), P-2 is checked on the nominal and becomes a
per-leg bound `τ(t_start + n) ≥ n h − Λ_i`. Here `Λ_i` is the certified lag of leg `i`. In the
nominal run the total lag per leg start is about 0.1–0.2 s (418 ticks below 0.8 across 8 legs).

**Lemma P-3 (arrival).** The S-curve library (shared with `nav_contract`) gives:

* `‖S(τ) − wᵢ‖ ≤ 0.1006 + float` at the blend parameter `τᵢ*` of corner `i`, so the target is within
  0.105 there (the corner cut, 4.4 mm of margin);
* `τᵢ* − τ_{i−1}* = Tᵢ^nom` (the nominal S-curve leg duration).

Combined with P-2, the target enters `nearT wᵢ 0.105` at a tick at most `Tᵢ^nom/h + Λᵢ/h` after it
entered `nearT w_{i−1} 0.105`.

The allowances against the nominal leg times (1.685, 1.933, 1.845, 1.854, 3.621, 1.852, 1.85,
1.85 s) leave **at least 0.92 s per leg**. That covers `Λᵢ` with a factor above 4. Leg 0 needs the
start transient (from `p`, with the speed ramp) and the time to reach the column top; the Monte
Carlo gives 1.36–1.70 s against 3 s.

**The nesting of `reachSeqF`** uses the arrival tick of the previous waypoint as the reference. The
proof constructs those ticks from the S-curve times: `τ(t)` is monotone, so the first tick at which
`τ ≥ τᵢ*` exists and is unique. The allowance counts from it.

**First leg and heading.** Heading enters only through `e` and `v` (3.8). The leg-0 pacing margin is
1.3 s. E4 must confirm it for `ψ₀ ≠ 0`.

**Hold part.** See 3.11. The `◇_[0,10800]` deadline has more than 4000 ticks of slack.

---

## 6. Lean structure

### 6.1 Files (new, under `Contracts/Track/`; no existing file changes)

| file | content |
|---|---|
| `Track/FloatBound.lean` | (P1) the rounding lemmas for `Float32` and `Float` on the core v4.36 model (port of the FloatModel layer); `FloatBound` (interval + error) and the `fl_bound` tactic; comparison and branch lemmas |
| `Track/LibmExt.lean` | the extension `LibmSpecTrack ⊇ LibmSpec`: `tanf` on `[0, π/4]`, `powf(·, 3)` accuracy; proofs that `expf` and `atanf` are not needed |
| `Track/Unconditional.lean` | (M1, M2) actuators in `[0, 1]`, integrators bounded; the `World` invariant `InvW` |
| `Track/Region.lean` | `D`, `D°` (16 conditions + Y1–Y5), as a `structure` over `(PState, World)`; projections to each function's `D_f` |
| `Track/Ideal/*.lean` | C1–C16, one file per class: `PosNE`, `PosD`, `Thrust`, `Attitude`, `Rate`, `Motors`, `AHRS`, `Nav`, `Glue`, `Takeover` |
| `Track/Plant/Sharp.lean` | (P4) the block one-step lemma of 3.7 (`step_pv_sharp`, `step_qw_gronwall`) |
| `Track/Linear/Model.lean` | the affine laws as real matrices `A_c, B_c`; the statement "tick on `D` = affine + w" |
| `Track/Linear/Cert.lean` | rational `P_c`, `L_c`, `D_c` (generated); the reflection checker `checkLDL : List (List ℤ) → … → Bool` with its soundness proof; `lyap_V`, `lyap_H`, `lyap_Y` |
| `Track/ISS.lean` | the discrete comparison lemma, geometric sums, ℓ1 convolution bounds, the tube lemma |
| `Track/Interval.lean` | dyadic intervals (`ℤ × ℤ` mantissa/exponent), outward-rounded `+ − × ÷ √`, sound enclosures of `sin/cos/acos/atan2` (Taylor with remainder from `Real.sin_bound` etc.), the per-tick checker of the nominal |
| `Track/Nominal/Leg0Cells.lean`, `Track/Nominal/Legs17.lean` | generated certificates: per cell and per 500-tick chunk, the enclosure of `ξ̂` and the checked transition |
| `Track/SCurve/*.lean` | the S-curve semantics: segment structure, jerk and acceleration limits, the corner blend bound (≤ `WP_RADIUS_M + 0.0006`), leg durations. Shared with `nav_contract` (developed once, in coordination) |
| `Track/Yaw.lean` | the heading subsystem contract (3.8) |
| `Track/Pacing.lean` | P-1, P-2, P-3 |
| `Track/Invariant.lean` | `Inv t`, the base case, the step, the induction to 12000 |
| `Track/Main.lean` | T1–T5 from `Inv`; `track_contract_proof`, used to discharge the `sorry` of `Sub.lean` (by the coordinator, as a separate edit) |

### 6.2 The induction

```
structure Inv (x : ℕ → X) (t : ℕ) : Prop where
  region : InRegion° (x t).phys (worldAt x t)      -- D° (worldAt from mem_Mctrl's hidden state)
  tube   : V (ξ (x t) - ξ̂ (phase x t)) ≤ tubeR t  -- 3.4
  phase  : PhaseOK x t                            -- leg index, S-curve time within Λ of nominal
theorem inv_zero  : x ∈ Mloop … → x ∈ Atakeoff → Inv x 0      -- with ticks 0,1 by direct evaluation
theorem inv_succ  : x ∈ Mloop … → Inv x t → t < 12000 → Inv x (t+1)
theorem inv_all   : … → ∀ t ≤ 12000, Inv x t                   -- Nat.rec
```

`worldAt x t` is the hidden state of `mem_Mctrl`'s witness. Its uniqueness, from the determinism
of `tickT`, needs a small lemma, because `mem_Mctrl` is an existential.

T1–T4 then follow tick by tick from `Inv`. T5 follows from `Inv.phase` and P-3, and the hold from
3.11.

### 6.3 Library use

* **DynamicalSystems.**
  * Useful: the vocabulary `IsInvariantOn`, and `Function.autonomousFlow`, already used for
    `sampledFlow` (ι = ℕ), for the hold phase.
  * Partly useful: `IsLyapunovOn` for the qualitative monotonicity of `V` after the target stops.
  * Not usable for the quantitative core:
    * its Lyapunov and LaSalle theorems are qualitative (ε–δ stability, convergence) and autonomous;
    * ISS is only a `proof_wanted` (`ComparisonFunctions.foo`);
    * the input-output small-gain theorems are global `Lp` statements on measure spaces, with
      causality left as `proof_wanted`.

  The class-K/KL structures (`MemK`, `MemKL`) can state the tube bound if desired. A plain
  `λ^t`-form is simpler and is what the checker produces.
* **Mathlib.**
  * Grönwall: `norm_le_gronwallBound_of_norm_deriv_right_le`, `gronwallBound_of_K_ne_0`, and
    `dist_le_of_approx_trajectories_ODE` for the `(q, ω)` block;
  * `image_norm_le_of_norm_deriv_right_le_deriv_boundary`, already used in `Euler.lean`;
  * `Matrix` with `Matrix.PosSemidef` and `Matrix.posSemidef_conjTranspose_mul_self`, for the
    `L D Lᵀ` certificate. The checker proves the identity
    `λ²P − AᵀPA = L D Lᵀ` over ℤ (scaled) and `D ≥ 0`;
  * `tsum_geometric_of_lt_one`, `Finset.abs_sum_le_sum_abs`;
  * `Real.sin_bound`, `Real.cos_bound`, `Real.arccos` monotonicity, `Complex.arg` facts, for the
    libm enclosures.
* **Own code** (about 300 lines): the discrete comparison lemma
  `V(k+1) ≤ λ V(k) + c(k) → V(n) ≤ λⁿ V(0) + Σ λ^{n−1−k} c(k)`, by `Nat.rec`.

### 6.4 Numeric constants: how each is checked

| kind | examples | method |
|---|---|---|
| scalar inequalities | `ρ + δ ≤ 0.25`, `D` margins, `α = dt/(dt + RC)` bounds, IMAX comparisons | `norm_num` |
| float literals | `Float32` constants of the parameters (`ATC_RAT_RLL_P = 0.135000005…`) | read from `MissionWorld` by the `construct` evaluation. **Obstacle:** `construct` does not reduce in the kernel (MISSION.md). Prove instead lemmas `MissionWorld w₀ → w₀.ap._pid_rate_roll._kp = 0x3E0A3D71` etc. by unfolding `construct` and `VehicleParams.set` symbolically: the parse path `toF32` must reduce for these literals. If it does not, state the parameter values as part of a strengthened `MissionWorld'` and check them with `mission_world_check`. **Decide this early (M0).** |
| matrix certificates | `P_c`, `L_c`, `D_c` (V: 8×8, H: 32×32 real, Y: 8×8) | generated in Python (exact rationals from SciPy's float solution, rounded, with the LDL computed exactly in `fractions`); checked in Lean by `decide` on a Boolean checker over `List (List ℤ)` (entries scaled to integers) with a soundness theorem. Kernel `Nat`/`Int` arithmetic is GMP-backed, so a 32³ check is seconds. No `native_decide`: it would add `Lean.ofReduceBool` and break the axiom audit |
| ℓ1 and finite-horizon gains | `Σ_{k<N} ‖C A^k B‖` | the same reflection checker over dyadic intervals, `N` up to about 3000 (the vertical impulse response decays to 10⁻³ by tick 2793) |
| the certified nominal | `ξ̂_t` over about 1200 ticks × about 800 cells (leg 0), about 10000 ticks once (legs 1–7, hold) | the per-tick interval checker, in chunks of 500 ticks per theorem (parallel build). **Cost risk:** about 10⁷ dyadic operations in the kernel. Estimate and prototype in M0 (E5) |
| libm enclosures inside the nominal | `sin`, `cos`, `acos` of the thrust angle | Taylor enclosures with Mathlib's bounds, plus `LibmSpec` accuracy |

---

## 7. Risks

| # | risk | where the statement might be false or unprovable | evidence | mitigation |
|---|---|---|---|---|
| R1 | **T1 margin** | `δ = 0.095` against 0.087 nominal; the worst start (lowest, 0.8 m climb) is the nominal one by the profile scan; the margin is about 9 mm | nominal 0.0870; linear model 0.0862; peak decreases with shorter climbs; no Monte Carlo error data | E1 (Monte Carlo with the target recorded); if `max err > 0.09`, rebalance `δ' ≤ 0.14`, `ρ' = 0.25 − δ'` (nav measured 0.071) |
| R2 | **T1 by gains** | an ISS/ℓ1 bound gives ≥ 0.116 for vertical alone | finding 3 | the two-layer architecture (3.5) |
| R3 | **T4 directional** | false for an isotropic bound; true with 1.85–2.35 cm margins on the nominal; unmeasured for other starts and headings | 2.1 | the certified nominal at each corner; E1, E4 |
| R4 | **δ₀ at corner starts** | the cap 0.0364 is geometric; the climb error in the active phase is about 0.01 by the model; not measured | linear model; nominal 0.012 up to 0.37 m of climb | per-cell certificates; E1 with the 8 box corners × 8 headings |
| R5 | **pacing under worst starts** | leg 0 depends on the start transient (the freefall Monte Carlo fails 39 %); with the hover start, slack ≥ 1.3 s; leg 1 slack ≥ 0.92 s | 2.2 | the scaler in the nominal; E4 for headings |
| R6 | **heading transient** | the yaw turn up to π lasts about 3 s, overlapping the leg-1 corner; inflates the H tube; the π branch cut; turn-direction choice at exactly π (Y5) | none (all Monte Carlo runs at ψ₀ = 0) | E4; the Y lemma; state heading statements modulo 2π |
| R7 | **target corner cut** | T5a needs `‖S(τᵢ*) − wᵢ‖ ≤ 0.105`; measured 0.10002–0.10056 (4.4 mm of margin); float S-curve evaluation (powf) | 2.1 | S-curve library; `powf` hypothesis |
| R8 | **hold stopping point** | needs phase-resolved `err + |v|/kP ≤ 0.105` at completion; global δ is not enough | measured 0.028 | the nominal at `t_c`; the "never completes" case is trivial |
| R9 | **float cancellations** | `acosf(dot ≈ 1)` in the thrust-vector code; division by small `|vel_T|` in the scaler and `limit_accel_xy` | analysis 4 | state β on rotation vectors and clamped outputs |
| R10 | **plant model mismatch with the evidence** | all data is PyBullet (substeps, backward-difference specific force, ground); the theorem is the exact flow | PLANT.md, "Where the model differs" | E3: a model-faithful simulator (RK4 at 10 kHz of `vf`, ZOH, instantaneous specific force) driving `copter_lean` |
| R11 | **trim offset** | `MOT_THST_HOVER = 0.4444` against `1/2.25` gives about 10⁻³ m/s² of bias; absorbed by the integrator; harmless | — | include in `w` |
| R12 | **parameter literals** | `construct` does not reduce in the kernel, so the gains must be obtained symbolically | MISSION.md | M0 decision (6.4) |
| R13 | **kernel cost of certificates** | the nominal over about 2·10⁶ tick-cells may be too slow without `native_decide` | — | E5 prototype; chunking; exploiting linearity in leg 0 (the response is linear in the direction weights) to reduce the cells to the 1-parameter `L` |
| R14 | **sqrt-controller linear zones** | D6 needs `|e| ≤ D1_max/kp²` for `AC_P_2D`/`AC_P_1D` and for the navigator's shaping; the `D1_max` values are not yet extracted | — | E2 reads them from `--print-params` plus the `set_limits` calls; if a zone is smaller than δ, that `sqrt_controller` branch must be modeled (it is monotone and bounded) |
| R15 | **joint decomposition** | `track_contract` needs S-curve facts that `nav_contract` also proves; double work if developed separately | — | one shared `SCurve` library |

---

## 8. Effort and order of attack

### 8.1 Effort per part

Person-weeks for one Lean and control expert using agents for the controller unfolding. The
ranges reflect the risks above.

| part | content | weeks |
|---|---|---|
| P0 | experiments E1–E6 (Python, no Lean) and the certificate generators | 3–4 |
| P1 | float layer port and `fl_bound` tactic | 3–5 |
| P2 | M1, M2 (unconditional) | 2–3 |
| P3 | controller lemmas C1–C16 | 10–16 |
| P4 | plant sharp step (3.7) | 2–4 |
| P5 | linear models, Lyapunov certificates, reflection checker | 4–6 |
| P6 | attitude and rate loop (M4) | 4–6 |
| P7 | vertical loop (M5) | 3–5 |
| P8 | horizontal loop and heading subsystem (M6) | 6–9 |
| P9 | S-curve library (shared with nav) | 8–12 |
| P10 | interval nominal: leg-0 cells, legs 1–7, merging | 6–10 |
| P11 | T3, T4, T5, hold, the invariant and the assembly | 5–8 |
| **total** | | **56–88** |

Calendar time with 3–4 agents in parallel on P3/P9/P10: about 5–8 months.

### 8.2 Milestones

Each milestone is a sorry-free theorem of independent interest, in this order.

* **M0 (decision gate, weeks 0–4).** Run E1–E6. Decide:
  1. whether to keep `δ`, `ρ` or rebalance;
  2. the parameter-literal route (6.4);
  3. the kernel cost of the nominal checker (E5).

  No Lean theorem. Output: the final `D` thresholds and certificates.
* **M1. Actuators always in `[0, 1]` and finite** (unconditional, every reachable world).
  `∀ w smp, InvW w → InvW (tick w smp).1 ∧ ∀ i : Fin 4, F32Bd (actVec (tick w smp).2)[i] 1 ∧ 0 ≤ …`.
* **M2. Integrators and filters bounded** (unconditional). `|I| ≤ IMAX` for all six PIDs; the
  throttle filter in `[0, 1]`.
* **M3. The plant sharp step** (3.7), a stand-alone plant-library result.
* **M4. The attitude loop tracks the tilt command.** For the plant's attitude block in closed loop
  with C9–C12 and any thrust-vector command sequence with `|a_NE| ≤ 4`, `|Δa_NE| ≤ j h`, and any
  heading command:
  * tilt error ≤ ε_att (target about 1.5°);
  * `|ω| ≤ W`;
  * actuators in `[0.30, 0.62]`;
  * no saturation flag.

  This is an inner-loop contract of independent value: it is the "attitude controller is good"
  theorem.
* **M5. Vertical loop contraction.** With the tilt as a bounded input from M4:
  * the vertical certificate `lyap_V`;
  * the ISS bound;
  * the certified response to the leg-0 climb family (the 1-parameter `L`).

  Output: `|e_z| ≤ δ_z(L)` with the signed profile.
* **M6. Horizontal loop and heading.** `lyap_H`, the heading-subsystem contract (3.8) and the H ISS
  bound with heading coupling as an input.
* **M7. S-curve library** (with nav). Corner-cut bound, leg durations, `pos_T = S(τ)` per tick.
* **M8. Pacing.** P-1 to P-3 on the certified nominal; T5a.
* **M9. Full ψtrack.** The invariant, T1–T5, the hold, `track_contract`.

---

## 9. Experiments to run first (P0)

The scripts used for this plan are in the scratchpad:

* `/private/tmp/claude-501/-Users-ryan-Research-delegate/547e050f-c29a-418f-816a-16412bc752a6/scratchpad/vert.py`
  (vertical linear model against `flight.csv`);
* `/private/tmp/claude-501/-Users-ryan-Research-delegate/547e050f-c29a-418f-816a-16412bc752a6/scratchpad/vgain.py`
  (ℓ1 gains);
* `/private/tmp/claude-501/-Users-ryan-Research-delegate/547e050f-c29a-418f-816a-16412bc752a6/scratchpad/vprof.py`
  (peak error against climb length).

The experiments:

* **E1. Monte Carlo with the target recorded.** Rerun `montecarlo.py` (lean vehicle) with
  `--trace`, so that per tick the target and the error are logged. Report, over the box (including
  the 8 corners):
  * max err;
  * max err in the T3 region;
  * T4 margins per waypoint;
  * the corner cut per waypoint;
  * the actuator range;
  * the maximum of every `D` quantity.

  This decides R1, R3, R4 and R7.
* **E2. Linear channel models** for H and Y, as done for V, validated against `flight.csv`. Report:
  * `P_c`, `λ_c` and ℓ1 gains;
  * the `D1_max` and `linear_dist` of every sqrt controller (R14).
* **E3. Model-faithful plant.** RK4 at 10 kHz of `vf` with ZOH, the instantaneous specific force and
  no ground, driving `copter_lean`. Repeat E1 on it; the constants must hold here, not only in
  PyBullet (R10).
* **E4. Heading Monte Carlo.** `ψ₀ ∈ {0, ±π/4, ±π/2, ±3π/4, π}` × the 12 worst-case starts, plus
  200 random `(p, ψ₀)`. Report the E1 quantities, the maximum `|r|`, the yaw saturation flags, and
  the leg-0, leg-1 and leg-2 times (R6).
* **E5. Kernel cost prototype.** A dyadic-interval checker of 500 ticks of the V channel (8 states),
  timed with `lake env lean`, extrapolated to H (32 states) and to the cell count (R13).
* **E6. Parameter literals.** Check whether `MissionWorld w₀ → w₀.ap._pid_rate_roll._kp = …`
  can be proved by unfolding `construct` on the embedded text (R12).
