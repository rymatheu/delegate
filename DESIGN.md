# leanfc: a compact cascade flight controller in Lean 4

The smallest complete flight stack that is a research test bench. It has:

- waypoint navigation with two kinds of leg, as ArduPilot's Waypoint and Spline navigation offer them:
  straight `WAYPOINT` legs and curved `SPLINE` legs, both one cubic Hermite curve (`Leanfc/Path.lean`),
  with the heading following the path (ArduCopter's default `WP_YAW_BEHAVIOR` 1);
- state estimation: an error-state EKF, the estimator of both vehicle files, with the fixed-gain
  filters kept as a baseline (selected by the `estimator` parameter);
- position and velocity control;
- attitude and rate control, with the navigator's yaw rate as feedforward;
- motor mixing;
- a vehicle layer around that flight law: arming with pre-arm checks, ArduCopter's flight modes
  (STABILIZE, AUTO, GUIDED, LOITER, RTL, LAND, BRAKE), takeoff from the ground, landing with a
  touchdown detector and the automatic disarm, missions uploaded at run time, failsafes;
- a MAVLink interface by ArduCopter's conventions, so that an unmodified QGroundControl flies it;
- one main loop.

It is configured by a parameter file and flown in a rigid-body simulator with a sensor model, running
deterministic or noisy. The controller is Lean code over FloatLib's `Binary32`. The simulator is
gym-pybullet-drones (PyBullet), driven by a Python harness that also models the sensors and the motor
lag.

The design follows `pyfc` (the Python prototype at `/Users/ryan/Research/delegate/staging/pyfc/`; read
its README.md and every file in `pyfc/`) and ArduCopter's cascade: feedforward at every stage, the
thrust-vector handoff from acceleration to attitude, and Quad-X mixing. The plant used for proofs is
not here; it is the continuous CF2X ODE in cpp2lean's contracts package.

## Architecture

Two processes in lock step, one line each way per 400 Hz tick:

1. **The controller**, `.lake/build/bin/leanfc` (Lean, binary32). `Main.lean` reads the parameter
   files given with `--params` once at startup. `ParamFile.load` builds one `Params` value from them,
   computing every derived constant there. `Main.lean` then reads one line of 16 sensor decimals per
   tick, rounds each once to binary32, runs one pure tick and prints the four motor commands
   (with `--trace` and `--bits`, also the estimates, the target, the leg, the heading setpoint and the
   hex words; with `--trace-vehicle` the mode, armed, landed state and mission item).
   The tick is three pure layers:

   - **services** (`Leanfc/Mavlink/Gcs.lean`, only with `--mav`): the MAVLink protocols (parameters,
     mission, commands, streams) turn at most one received message into outgoing messages and
     `Command`s for the vehicle, from the vehicle's `Telemetry` of the previous tick;
   - **vehicle layer** (`Leanfc/Copter/*`): applies the commands (arming, modes, takeoff, missions,
     go-to, home, speed, parameters) by ArduCopter's rules, runs the failsafes, and chooses the output
     law of its phase: motors off or at idle on the ground, the takeoff throttle ramp, the navigator on
     its legs, braking, the landing descent;
   - **flight law** (`Controller.lean` and the modules under it): estimator → navigator → position →
     attitude → mixer.

   `Leanfc/Autopilot.lean` composes the three. The IO shell is `Main.lean` (arguments, files, the
   lock-step loop) and `Shell/` (text formatting, the UDP socket with its receiver thread, the MAVLink
   test drivers). Without `--mav` no socket exists and the run is deterministic.
2. **The harness**, `sim/run_leanfc.py` (Python, binary64). It reads the same parameter files for what
   it needs: `dt`, `dtFix`, the start point, the waypoints, and `SIM_VEHICLE`, which picks the URDF.
   It runs gym-pybullet-drones `CtrlAviary` (subclass `LeanfcAviary`) with `Physics.PYB`, 1200 Hz
   physics and the 400 Hz control step's RPMs held over 3 substeps, at gravity 9.80665. The setup is
   cpp2lean's `sim/run_copter.py` (`place`, `reset_env`, `actuators_to_rpm`, `sim_state`,
   `SpecificForce`, `enu_state_to_ned`, `quat_ned_frd` imported unmodified). Each tick it turns the
   true state into sensor readings (the sensor layer, below), sends them, reads the motors and steps
   the physics. It writes one CSV row per tick and a JSON sidecar (vehicle, parameter files, noise,
   seed, fix rate, motor lag, start, waypoints, wall time), which `sim/analyze.py` reads.

### The tick protocol

Input, one line per tick: `gx gy gz ax ay az fix hc hs pn pe pd vn ve vd vfix`, optionally followed by
a 17th number `pfix` (position-fix presence, default 1; the harness sends 0 during a GPS dropout, when
the heading stays and the position and velocity fixes are absent). These are the gyro
(rad/s, body FRD), the specific force (m/s², body FRD), fix presence (with 0 the heading and the
position fix are absent), the heading (cos ψ, sin ψ), the position fix (NED m), the velocity fix
(NED m/s) and velocity-fix presence.

Output: `m1 m2 m3 m4` in Quad-X slot order. With `--trace` it is followed by p̂, v̂, q̂ of the active
estimator, the target pSp and the leg; `--trace-ekf` appends the diagonal of P (15) and the gyro and
accelerometer bias estimates (zeros for P with the fixed estimator, which reports its attitude filter's
gyro bias and its nav filter's NED acceleration bias). With `--trace` the line ends with the heading
setpoint (cos ψ, sin ψ), after the `--trace-ekf` fields, so every earlier field keeps its position; the
harness writes it as the last two CSV columns `hsp_c`, `hsp_s`. Numbers print with 9 significant digits,
which round-trips binary32.

`--calibrate N` takes the gyros of the first N lines as at-rest samples, after which the controller
prints `calibrated`. A malformed line gets zeros and does not advance the state.

### The sensor layer (harness)

- gyro = body rates + bias + white noise;
- accel = R(q)ᵀ · (earth-frame specific force) + bias + white noise;
- on fix ticks (every dtFix/dt ticks): heading of the true yaw plus noise, position (σ north/east,
  σ down) and velocity.

The bias directions are constant per run, and all noise comes from `numpy.random.default_rng(seed)`.
There are two profiles:

- `none`: zero noise, with the `params/mocap.params` overlay (100 Hz fixes, mocap navigation gains);
- `field`: pyfc `Noise()`, with the vehicle file's 10 Hz fixes and field gains.

### The vehicle parameter

The vehicle is data, not code. `Leanfc/Vehicle.lean` defines the `Vehicle` structure (mass, diagonal
inertia, motor offset l, km/kf, T_max, and the inverse allocation rows derived from them by
`Vehicle.make`). Its values come from the parameter file. `Params.vehicle` is read by `Position.step`
(mass), `Attitude.step` (inertia) and `Mixer.step` (inverse rows, T_max).

Two vehicles ship:

- `params/x500.params` (Holybro X500 V2, from PX4's Gazebo model) and `sim/assets/x500.urdf`, loaded
  by `LeanfcAviary` without modifying the package;
- `params/cf2x.params` (Crazyflie 2.X, the package's `cf2x.urdf`).

For the X500 the harness applies a first-order motor lag to each propeller's thrust (0.0125 s rising,
0.025 s falling) at every 1200 Hz substep. README.md has the numbers and their sources.

## Principles

1. One module per file, one `structure` for each module's state, one pure `step` function per
   module: `step (params) (state) (inputs) : state × outputs`. No `IO` anywhere except `Main.lean`
   and `Shell/`. Every function of the library is total (folds over bounded arrays, fuel-bounded
   recursion in the frame parser); the only `partial def` is the codec test driver's input loop in
   `Shell/Tools.lean`, and the lock-step loop is the IO shell's `repeat`.
2. The controller's scalar type is FloatLib's `Binary32` (`abbrev R := Binary32` in `Scalar.lean`).
   Every controller operation is one of `+ - * /`, `ExecFloat.sqrt`, `min`, `max`, comparison, and
   constants.

   **No transcendental functions in the controller** (no sin, cos, atan2, exp):

   - the quaternion step is the first-order update followed by normalization;
   - headings are carried as unit vectors (cos ψ, sin ψ), and the heading error is a cross product;
   - the heading setpoint turns by first-order rotations h ← normalize(h + ρ dt h⊥); the slew compares
     the cross and dot products of setpoint and target and bounds the remaining angle below by |x|
     (or 2 − |x| beyond 90°), so no angle is ever computed.

   So every operation has a FloatLib specification and rounding theorem, and reasoning about the
   controller uses FloatLib (`ExecFloat.Proof.*_eq_spec`, `Model.toReal_*_eq_roundAt`, ...) and
   nothing else.
3. Every number of the configuration comes from the parameter file, rounded once from decimal text
   to binary32. Constants derived from it are computed once at load time, in binary32, by the
   modules' `make` functions (the navigator's legs, tangents, chord lengths, speed limits and end
   speeds included); a tick does no setup work. The exceptions are gravity 9.80665, 2π (the rate
   low-pass), the 2 of the heading slew's angle bound (2 − |x|), the Hermite basis coefficients
   (1, 2, 3, 4, 6, 12), the 16 curvature samples of a spline leg, the floor 1e-3 on ‖p′(τ)‖ and the
   numeric tolerances, which are literals in the code. The vehicle layer computes the legs of a new
   path (`Navigator.withLegs`, which is `Navigator.make`) once when the path starts (a mode change, a
   mission item, a go-to, a change of speed), never in the ticks between; its literals are ArduCopter's
   constants (the 1 s and 0.2 s of the touchdown detector, the 4 s pause of a failsafe landing, the 2 s
   estimator settling, a tenth of `nav.vMaxZ` as liftoff climb rate) and leanfc's thresholds (0.9 of the
   hover thrust and 0.25 m/s for the touchdown, 30° and 0.2 rad/s / 0.5 m/s for the pre-arm level and
   rest checks).
4. The physics, the sensor noise and the motor lag live in the harness (binary64, transcendentals
   allowed), never in the controller.
5. Smallest possible: no features beyond what the acceptance tests need.
6. No `sorry`, no `native_decide`, no axioms beyond the standard three in any theorem added.
7. The vehicle layer follows ArduCopter (checkout 802db19de1, 4.8.0-dev): its parameter names, meanings
   and defaults, its mode rules and status texts, its takeoff, landing and failsafe sequences. Where
   leanfc differs (no RC, so STABILIZE does not fly; consecutive waypoint items flown as one path; a
   brake before every new path) README.md says so. Timers are natural-number tick counts computed at
   load time from the parameters (exact rational conversion), never accumulated binary32 time.

## Conventions

World frame NED (north, east, down); body frame FRD (front, right, down); the quaternion (w, x, y, z)
rotates body vectors into the world. Gravity g = 9.80665 along +down.

Motors are in ArduPilot Quad-X order, which is also PX4's:

- slots 1..4 sit at +45°, −135°, −45°, +135° from the nose;
- motors 1 and 2 spin CCW, 3 and 4 CW;
- with l the offset per axis (arm/√2), the motor positions (x, y) are (l, l), (−l, −l), (l, −l),
  (−l, l);
- the torque of motor i with thrust T_i along −z_body is (−y_i T_i, x_i T_i, s_i c T_i), with
  s = (+1, +1, −1, −1) and c = km/kf.

A motor command m ∈ [0, 1] is the fraction of the maximum per-motor thrust T_max. Hover is
m g / (4 T_max): 1/2.25 for the CF2X and 0.592 for the X500.

## Files

| file | contents |
|---|---|
| `Leanfc/Scalar.lean` | `abbrev R := Binary32`; `R.ofFloat : Float → R` (round to nearest), `R.toFloat : R → Float`; `sqrt`, `abs`, `clamp lo hi`; `gravity` |
| `Leanfc/Vec3.lean` | `structure Vec3 (x y z : R)`; add, sub, neg, scale, div, hadamard, dot, cross, norm, `clampNorm`, `clampXY`, `clampAxes`, zero |
| `Leanfc/Quat.lean` | `structure Quat (w x y z : R)`. mul, conj, rotate (q v q⁻¹), normalize. `integrate q ω (dt/2)` = normalize (q + ½ q ⊗ (0, ω) dt). `headingVec q`: the body x axis projected to the horizontal plane and normalized, (cos ψ, sin ψ), or (1, 0) if its norm is below 1e-6. `fromThrustHeading zb (hc, hs)`: y_b = zb × (hc, hs, 0) normalized, x_b = y_b × zb, then Shepperd's method. `errorVec q_hat q_des` = 2 · vector part of q_hat⁻¹ ⊗ q_des, negated if its w is negative |
| `Leanfc/Vehicle.lean` | `Row4`; `structure Vehicle` (mass, inertia, l, kmKf, tMax, inverse rows); `Vehicle.make` computes the closed-form inverse T/4 ∓ τx/(4l) ± τy/(4l) ± τz/(4c), i.e. the entries 1/4, 1/(4l), 1/(4c); `allocRows` (A, for checks and `--print-params`) |
| `Leanfc/PI.lean` | `structure PIGains (kp ki iMax kiDt : R)`, `PI.gains kp ki iMax dt`; `structure PIState (integral : Vec3)`; `step1` (one axis) and `step` (three axes): integral ← clamp (integral + ki dt e) to ±iMax, output kp e + integral |
| `Leanfc/Path.lean` | `structure Hermite (p0 m0 p1 m1)`; `line a b` (tangents b − a); `eval` p(τ) = (h00 p0 + h01 p1) + (h10 m0 + h11 m1), exact at τ = 0 and 1 (end points stored as w + 0); `deriv` p′, `deriv2` p″, `curvature` ‖p′ × p″‖/‖p′‖³ |
| `Leanfc/Navigator.lean` | `LegKind` (line, spline), `Waypoint` (pos, kind, stop), `Leg` (kind, curve, chord length, vLeg, vEnd, (vEnd + aMax dt/2)², passed); `NavParams` (vMax, aMax, aLat, vMaxZ, radius, lagMax, the yaw parameters, `legs`, derived aMax·dt, aMax·dt/2, 2·aMax, lagMax², radius², yawAccelMax·dt, 2·yawAccelMax, (yawSpeedMin·vMax)²); `legsOf`/`make` (tangent rules: t0 = end direction of the previous leg if its waypoint is passed, else the chord; t1 = chord if the leg ends at rest, else the next segment's direction (next leg a line) or (next waypoint − origin) (Catmull–Rom); a leg ends at rest at the last waypoint, at `stop` and between two lines; vLeg = min(vMax, vMaxZ / max \|p′z\|/‖p′‖, sqrt(aLat/κmax)) over τ = j/16; vEnd backward with the braking curve B(v, d) = sqrt((v + aMax dt/2)² + 2 aMax d) − aMax dt/2); `NavState` (leg, τ, u, target, vFF, heading, yaw rate); `step`: u moves by ≤ aMax·dt toward min(vLeg, B(vEnd, ‖dest − target‖)) (0 while the lag exceeds lagMax), τ ← min(1, τ + u dt / max(‖p′(τ)‖, 1e-3)), target p(τ), vFF = u p′/‖p′‖, aFF = ΔvFF/dt; a passed waypoint starts the next leg in the same tick (τ = 0, same u); at a rest point the remaining u goes to 0 at aMax·dt per tick and the target waits until the vehicle is within radius; `slewHeading` unchanged; `withLegs` (the legs of a run-time mission, `make` with the same parameters), `brakeTarget`/`brake` (u falls by aMax·dt per tick along the current leg, then the target holds) |
| `Leanfc/AttitudeFilter.lean` | Mahony explicit complementary filter with bias: state (q, bias, omegaFiltered); params kAcc, kYaw, kBias, cutoffHz plus the derived kYaw/kAcc, dt/2 and a/(1+a), a = 2π·cutoffHz·dt (`make`). Correction err = downMeas × downPred, plus the heading term (kYaw/kAcc) · rotate(q⁻¹, (0, 0, hs·ĉ − hc·ŝ)) on fix ticks. bias −= kBias·err·dt; rate = gyro − bias; q = integrate q (rate + kAcc·err); omegaFiltered += a/(1+a) (rate − omegaFiltered) |
| `Leanfc/NavFilter.lean` | state (p, v, aBias); params alpha, beta, kV, kB plus the derived beta/dtFix, kB/dtFix, dt²/2 (`make`). Prediction a = rotate q accel + (0, 0, g) − aBias; p += v dt + a dt²/2; v += a dt. On a position fix, r = fix − p: p += alpha r, v += (beta/dtFix) r. On a velocity fix, rv = fix − v: v += kV rv, aBias −= (kB/dtFix) rv |
| `Leanfc/Position.lean` | pyfc `position.py`: vSp = kpPos (pSp − pHat) + vFF, clamped in the plane (vMaxXY) and vertically (vMaxZ); aSp = PI(vSp − vHat) + aFF, clamped (aMaxXY, aMaxZ); f = aSp − (0, 0, g) with f.z ≤ −g/2; thrust = mass ‖f‖ (the vehicle's mass); qDes = fromThrustHeading (−f/‖f‖) heading, the navigator's heading setpoint |
| `Leanfc/Attitude.lean` | pyfc `attitude.py` with separate yaw gains and a yaw-rate feedforward: e = errorVec qHat qDes; ff = rotate (qHat⁻¹) (0, 0, yawRate) (the navigator's yaw rate in body axes, R(q̂)ᵀ e_z yawRate); omegaSp = clamp per axis ((kpAtt e.x, kpAtt e.y, kpYaw e.z) + ff, ±rateMax); torque = J · PI(omegaSp − omegaHat), with the gains `rate` on roll and pitch and `rateYaw` on yaw (J diagonal, the vehicle's) |
| `Leanfc/Mixer.lean` | `structure Motors (m1 m2 m3 m4 : R)`; `step v thrust torque` = clamp ((v's A⁻¹) [T, τx, τy, τz] / tMax) to [0, 1]; `allocate` (A · thrusts, for the checks) |
| `Leanfc/EKF.lean` | the 15-state error-state EKF, the operation-for-operation port of pyfc `ekf.py`: `Config` (the file's 1σ values), `Params` (+ derived Q per tick, R, initial P, low-pass, by `make` in binary32), `State` (q, v, p, bg, ba, ω̂, P as `Vector (Vector R 15) 15`). `init`, `calibrate` (bias = mean, prior variance max(σ_gyro²/n, σ_min²)), `predict` (mechanization, P ← (Φ(ΦP)ᵀ)ᵀ + Q, `sym`), `update` (scalar update + injection), `updateHeading`, `step` (predict, position N/E/D, velocity N/E/D, heading) → (q̂, ω̂, p̂, v̂) |
| `Leanfc/Controller.lean` | `inductive Estimator` (fixed, ekf). `structure Params`: vehicle, dt, dtFix, estimator, the module params (attFilter, navFilter, ekf, ...), start, waypoints, initial heading setpoint (hc, hs). `EstState` (the active estimator's state: fixed (att, nav) or ekf), `structure State`, `structure Sensors`. `init P`, `calibrate`: mean gyro at rest → bias (and the EKF's bias prior), `estimate` (p̂, v̂, q̂). `step : Params → State → Sensors → State × Motors`, the one tick: estimator (dispatched once) → navigator (target, feedforward, heading setpoint, yaw rate) → position (heading) → attitude (yaw rate) → mixer. `step` is `estimateStep` (the estimator, dispatched once) → `Navigator.step` → `track` (position → attitude → mixer), the same arithmetic as before the split; also `level` (level attitude at a heading with a given collective, rate integrator reset: the takeoff ramp), `idle` (every motor at one command, both integrators reset), `initAt` (the estimator started at a position and attitude), `rates` (ω̂); `Params.copter` (the vehicle layer's parameters) |
| `Leanfc/ParamFile.lean` | `Decimal.parseR` (decimal text → binary32, one rounding) and `tokens`; `ParamFile.names`; `parseFile` (errors with file:line; also the `estimator fixed\|ekf` line); `build` (validation, including `nav.yawBehavior` ∈ {0, 1}, and every `make`); `load` (several files, later ones override); `Raw`, `merge` (the merged raw values of several files; `ParamTable.Store.load` uses it), `complete`, `buildCopter` (the vehicle layer's ranges and tick counts), the `ORIGIN` line (`Decimal.parseScaled`, exact integers) |
| `Leanfc/Copter/Params.lean` | `CopterParams`: the vehicle layer's parameters (ArduCopter names: RTL_ALT_M, RTL_LOIT_TIME, LAND_SPD_MS, LAND_ALT_LOW_M, DISARM_DELAY, FS_GCS_ENABLE, FS_GCS_TIMEOUT, FS_EKF_ACTION, MOT_SPIN_ARM, MOT_SPOOL_TIME, TKOFF_SLEW_TIME, TKOFF_THR_MAX; leanfc's `copter.ekfPosMax`), each time also as ticks; `ticksOf` (exact: floor(x/dt + 1/2) on the rational values), `natOf?` |
| `Leanfc/Copter/State.lean` | `Goal`, `After`, `Phase` (ground, spool, ramp, path, brake, wait, descend, touchdown), `Boot` (calibrating, waitFix, running), `State`; `landedOf` (the landed state as a function of the phase); `initGround`, `initAir`; `startPath` (the navigator restarted at rest on new legs from the current target), `hold`, `disarm` |
| `Leanfc/Copter/Health.lean` | `Health.of` (calibrated, estimator started and settled, fix recency, EKF position covariance within `copter.ekfPosMax`, level within 30°, at rest), `prearm` (ArduPilot's texts), `sysStatus` (SYS_STATUS health bits, PREARM_CHECK) |
| `Leanfc/Copter/Land.lean` | the descent speed (LAND_SPD_MS below LAND_ALT_LOW_M, kpPos·(height − LAND_ALT_LOW_M) between it and `nav.vMaxZ` above) and the touchdown detector (thrust below 0.9 of hover and \|v̂z\| < 0.25 m/s for 1 s; "maybe landed" after 0.2 s) |
| `Leanfc/Copter/Plan.lean` | AUTO: `runEnd` (a run of consecutive waypoint items, ending after a hold), `startItem`, `rtlWaypoints`, `after` (what follows a brake or a wait), `pathDone` |
| `Leanfc/Copter/Modes.lean` | `enterMode` (the mode table), `apply` (one `Command`, one result), `landWithPause`, `setSpeed`, `armNow` |
| `Leanfc/Copter/Fly.lean` | `step` (fixes, boot calibration and estimator start, commands, failsafes, the phase's law and transitions, DISARM_DELAY), `telemetry` |
| `Leanfc/Mavlink/*.lean` | the MAVLink layer (README.md "MAVLink interface"): `Crc`, `Bytes`, `Messages` (generated by `sim/mavlink/gen_messages.py`), `Frame`, `Vehicle` (the `Command` / `Telemetry` contract), `Format` (geodesy, certified angles), `Mission`, `ParamTable`, `Gcs` (the services) |
| `Leanfc/Autopilot.lean` | `Autopilot.step`: services → vehicle layer → flight law in one pure tick; `run`: the vehicle without services |
| `Shell/Text.lean`, `Shell/Link.lean`, `Shell/Tools.lean` | IO helpers of `Main.lean`: the line format, the UDP link (receiver thread, frame log, the origin's cosine), the codec driver, `--bench`, `--selftest` |
| `Leanfc/Checks.lean` | `Bool` checks run by `Main --check` on the two shipped files (and, for the navigator, on the spline overlays and the X500 mixed mission): the CF2X file equals the build-time copy; hover command = the expected binary32 value per vehicle; allocation round trip (A · (A⁻¹ w) ≈ w within 1e-5); positive roll error gives positive roll torque; the attitude filter converges from 0.5 rad; the EKF's P stays exactly symmetric with a positive diagonal over 60 s at rest (X500 field and X500 + mocap configurations); the EKF converges from 5° tilt and 20° heading error with 3 m/s² north and east acceleration segments (X500). Navigator, per configuration (CF2X and X500 WAYPOINT square, SPLINE square, X500 mixed mission), the mission stepped open loop for 30 s with pHat = the previous tick's target, three lines: path ((1) every target of a Waypoint leg within 2 µm of its segment, (2) every leg's curve gives its origin at τ = 0 and its destination at τ = 1 bit for bit, legs chain bit for bit and every arrival in the run is the destination, (3) at passed waypoints the tangents agree and vFF turns no more and changes speed no more than in an ordinary tick), motion ((4) speed ≤ vMax, \|vFF.z\| ≤ vMaxZ, \|Δu\| ≤ aMax·dt every tick, u²κ ≤ 1.05 aLat on spline legs, (5) every leg that ends at rest arrives on its destination and holds it with vFF = 0 once u = 0, u = 0 nowhere else, (6) the mission completes at rest on the last waypoint) and heading (the setpoint ends each leg that ends at rest within 0.5° of its end direction, never turns faster than yawRateMax + 1e-4 rad/s, keeps its bits below the speed threshold); measured in binary64 (`Float.atan2`) in the check, not in the controller. The three small CF2X checks are also proved by `decide +kernel` |
| `Main.lean` | the IO shell (with `Shell/`). `--ground` (start on the ground), `--mav` and its link options, `--trace-vehicle`, `--codec`, `--bench`, `--selftest`; the batch start is the default. Arguments: `--params FILE` (repeatable), `--calibrate N`, `--trace`, `--trace-ekf` (diag P and the two bias estimates after the trace fields), `--bits`, `--ekf-only` (only the EKF, its whole state as hex words per tick, for the parity test), `--print-params` (with the derived legs as comments), `--check` (also loads `params/{cf2x,x500}-spline.params` and `sim/missions/x500-mixed.params`). Loads the configuration once, then the lock-step loop; the trace's leg index is the navigator's leg (= number of legs when the mission is complete) |
| `params/*.params` | `cf2x.params`, `x500.params` (complete, field profile; estimator ekf, `nav.yawBehavior` 1, the square as `WAYPOINT` legs, the vehicle layer's parameters), `ground.params` (ORIGIN at Pikes Peak, vertical speeds 1 m/s, FS_GCS_ENABLE 1), overlays `cf2x-spline.params`, `x500-spline.params` (the same points as `SPLINE` legs), `mocap.params` (100 Hz noiseless fixes, incl. the EKF's floored σ's), `fixed.params` and `ekf.params` (only the `estimator` line), `yawhold.params` (`nav.yawBehavior 0`) |
| `sim/run_leanfc.py` | the harness: `LeanfcAviary` (external URDF, motor lag), `make_env`, the sensor layer, the lock-step loop, CSV (last columns `hsp_c`, `hsp_s`, the heading setpoint, when the binary prints it) + JSON, `--motor-test`; `--estimator`, `--no-calibration`, `--dropout T0 T1`, `--trace-ekf`, `--record FILE`; `--ground` (resting on the ground plane, motor lag from zero), `--realtime SPEED`, `--mav` (`--mav-port`, `--mav-log`, `--origin`), `--trace-vehicle` (CSV columns `mode armed landed item`) |
| `sim/fly_qgc.sh` | the launcher for QGroundControl: the X500 on the ground, real time, MAVLink to UDP 14550 |
| `sim/mavlink/*` | `gen_messages.py` (the generator of `Messages.lean`), `test_codec.py`, `test_services.py` (QGroundControl's sequences against the real controller from the ground), `flight_metrics.py`, `run_qgc.py` (the real QGroundControl), `QGC.md` (the user's checklist), `QGC-REQUIREMENTS.md`, `LICENSES.md` |
| `sim/ekf_parity.py` | feeds one recorded sensor sequence to the Lean EKF (`--ekf-only`) and to pyfc `ekf.py` (imported read-only) and compares the state bit for bit every tick |
| `sim/ekf_runs.sh`, `sim/ekf_tables.py` | the estimator runs (both vehicles × both estimators × deterministic, field, no calibration, dropout; heading held with `params/yawhold.params`) and their tables (mean / worst over seeds) |
| `sim/nav_runs.sh`, `sim/nav_tables.py` | the default-configuration runs (both vehicles, WAYPOINT and SPLINE square, deterministic and field seeds 0..9, plus the deterministic test missions) and their tables |
| `sim/missions/*.params` | test missions (overlays): `{x500,cf2x}-mixed` (every transition between leg kinds, a stop mark), `{x500,cf2x}-collinear` (WAYPOINT, SPLINE, SPLINE on one line) |
| `sim/assets/x500.urdf` | the X500 in the format of the package's `cf2x.urdf` |
| `sim/analyze.py` | reads the CSV and its sidecar. Prints the metrics of pyfc `mission.py`/`noisy.py`: tracking error to the moving target (max, with where it occurs, and rms), the vehicle's closest approach to each waypoint (distance, time), the mission time (from when the vehicle stays within `nav.radius` of the last waypoint), the target path's largest distance from the straight polyline, hold error over the last 4 s, tilt, estimate errors, attitude error, saturated ticks; with the `--trace-ekf` columns also estimate errors against the start-of-tick truth, bias errors at the end and the fraction of position-error components inside ±3σ; with the `hsp_*` columns the heading tracking error (true yaw against the setpoint, rms and max) and the largest yaw rate. Writes a PNG (path top view, altitude, tracking error, motors) |
| `sim/mixer_inverse.py` | reference: the binary64 inverse and the binary32 hover command of each parameter file |
| `README.md` | what it is, how to build and run, the parameter file, the vehicles and their sources, the module table, conventions, tuning, results |

## Numeric and build facts

- **Toolchain.** `leanprover/lean4:v4.35.0`. `lakefile.toml` requires FloatLib pinned to commit
  `acba2057e452f32f4ed4f06bb0adbeda5342ba92`. `lakefile.toml` declares the libraries `Leanfc`, `Plant`
  and `Shell` and the executable `leanfc`; do not change its dependencies or `lake-manifest.json`, and do
  not run `lake update`.
- **FloatLib.** Import `FloatLib.Floats` and `open FloatLib.Floats`. `Binary32` is
  `ExecFloat.Binary (exponentBits := 8) (fractionBits := 23)`. These work on it: `+ - * /`, `<`, `≤`,
  `==`, `max`, `min`, negation and decimal literals. `ExecFloat.sqrt x` is the square root.
  `ExecFloat.Binary.ofFloat`/`toFloat` cross to binary64.
- **Speed.** Software binary32 operations cost 20 to 100 ns each. A 30 s X500 mission at 400 Hz runs
  in about 4 s, controller and PyBullet together.
- **Python.** `sim/.venv/bin/python`; build with
  `LEAN_NUM_THREADS=1 lake build`.

## Acceptance

1. `lake build` succeeds with no warnings about `sorry`.
2. `lake exe leanfc --check` prints each check with PASS.
3. `sim/run_leanfc.py --motor-test` passes for both vehicles. Each motor alone gives roll, pitch and
   yaw accelerations with the signs of its column of the Lean allocation matrix.
4. CF2X, `--vehicle cf2x --noise none`: all four legs reached, hold error below 10 mm, tracking
   error to the moving target below 0.1 m, zero saturated ticks. (pyfc gives 76 mm max, 2 mm hold.)
5. CF2X, `--vehicle cf2x --noise field --seed 0` (and seeds 1, 2): all four legs reached, hold error
   below 0.4 m, attitude estimate error below 2°, zero saturated ticks.
6. X500 with the motor lag, `--vehicle x500 --noise none`: all four legs reached, hold error below
   30 mm, tracking error to the moving target below 0.3 m, zero saturated ticks.
7. X500 with the motor lag, `--vehicle x500 --noise field --seed 0` (and 1, 2): all four legs reached,
   hold error below 0.5 m, attitude estimate error below 2°, zero saturated ticks.
8. Every number reported in README.md comes from these runs.
9. The default configuration of each vehicle file (estimator ekf, heading following the path) meets
   items 4 to 7, the field items on seeds 0..9.
10. `sim/ekf_parity.py` on a recorded field sequence: the Lean EKF equals pyfc `ekf.py` bit for bit on
    every tick, with the Lean derived constants installed in the Python object (ekf.py derives them in
    binary64).
11. `--check` includes the navigator checks (path, motion, heading) for both vehicles' WAYPOINT and
    SPLINE squares and the X500 mixed mission. (Until the leg kinds, the deterministic runs with
    `params/yawhold.params` reproduced the CSVs of the controller before the heading setpoint bit for
    bit; the new navigator ends each stop differently, so they no longer do, see README.md "Navigator".)
12. The SPLINE squares (`params/{cf2x,x500}-spline.params`) meet items 4 to 7 as well, and every
    waypoint of both squares is passed by the vehicle within `nav.radius` plus its tracking error.
13. The batch start (the default) gives byte-identical CSVs for the default missions of
    `sim/nav_runs.sh` before and after the vehicle layer: the vehicle layer in its batch state calls
    exactly `Controller.step`.
14. `sim/mavlink/test_codec.py` passes; `sim/mavlink/test_services.py` passes every step against the
    real controller flying from the ground (X500 deterministic and field seeds 0..4, CF2X
    deterministic), with the flight metrics of `sim/mavlink/flight_metrics.py`.
15. The real QGroundControl 5.1.5 completes its connect sequence against the real controller in the
    real-time simulation with every parameter loaded and no warning caused by leanfc
    (`sim/mavlink/run_qgc.py`).
