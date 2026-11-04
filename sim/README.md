# Closed-loop simulation of the Lean flight controller

This directory flies the quadcopter controller of `../Flight` (Lean 4) against the gym-pybullet-drones simulator, with the Crazyflie 2.x model in the X configuration (CF2X). The controller runs as a separate process and is the only controller in the loop: none of the controllers bundled with gym-pybullet-drones (DSLPIDControl and others) is imported or used. The simulator only integrates the rigid-body physics of the propeller RPMs it is given.

The controller can run in three ways, and all three produce the same motor commands bit for bit:

- `lake`: `lake exe flight` in the package root, the executable lake builds from the Lean sources.
- `bin`: `build/flight-c`, built by `build_c.sh` from the C files the Lean compiler emits, compiled and linked with the clang shipped in the Lean toolchain (`leanc`, clang 22.1.4). It needs no Lean or lake at run time.
- `interp`: `lake env lean --run Flight/Main.lean`, the same program run by Lean's interpreter.

## Setup

The simulator lives in a virtual environment `.venv` (Python 3.12, created with uv). gym-pybullet-drones is not on PyPI, so it is installed from the GitHub archive of the utiasDSL repository. PyBullet has no prebuilt wheel for this platform and is built from source; its bundled zlib defines `fdopen` as a macro that collides with the macOS SDK headers, which the `CFLAGS` setting below works around.

```
cd sim
/opt/homebrew/bin/uv venv --python 3.12 .venv
CFLAGS="-Dfdopen=fdopen" /opt/homebrew/bin/uv pip install --python .venv/bin/python pybullet
/opt/homebrew/bin/uv pip install --python .venv/bin/python \
  "gym-pybullet-drones @ https://github.com/utiasDSL/gym-pybullet-drones/archive/refs/heads/main.zip" \
  numpy matplotlib scipy
```

Installed versions: Python 3.12.13, gym-pybullet-drones 2.2.0 (GitHub main), pybullet 3.2.7, numpy 2.5.4, scipy 1.18.1, matplotlib 3.11.2. The package also pulls in gymnasium, torch and stable-baselines3, which this demo does not use.

The Lean side is built with `lake build flight` in the package root (toolchain `leanprover/lean4:v4.33.0-rc1`). The C route is built with `./build_c.sh`, which runs `lake build flight` first.

## The C route (`build_c.sh`)

Lake writes one C file per Lean module to `.lake/build/ir/Flight/` in the package root. The script copies the thirteen files in the import closure of `Flight.Main` to `build/c/` (so the exact C that was compiled stays next to the binary), compiles each with `leanc -c -O3 -DNDEBUG`, and links them with `leanc -O3 -o build/flight-c build/c/Flight_*.o`. `leanc` is the toolchain's wrapper around its clang; it adds the Lean include directory, `-ffp-contract=off` (no fused multiply-adds, so floating-point results follow the source operation by operation), and, when linking, the static archives of the Lean runtime and core library (`libleanrt.a`, `libInit.a` and the rest, see `leanc --print-ldflags`). `otool -L build/flight-c` lists only `/usr/lib/libc++.dylib` and `/usr/lib/libSystem.B.dylib`: the Lean runtime is linked statically, and only the macOS system libraries are dynamic (macOS does not support a fully static executable).

## Running

```
.venv/bin/python run_demo.py --backend lake      # or bin, or interp
.venv/bin/python run_demo.py --backend bin --gui # PyBullet window, paced to real time
.venv/bin/python run_demo.py --determinism       # fly all three backends and compare
```

The default mission is the figure-eight course: `params/cf2x.txt` (the tuned CF2X parameters, the file the Lean proofs mirror as `cf2xParams`) followed by `params/cf2x-course.txt`. Other options: `--params FILE` (repeatable; replaces the default pair, so `--params params/cf2x.txt` alone flies the three-waypoint corner mission), `--set "KEY VALUE..."` (extra override passed to the controller), `--duration` (default 30 s of simulated time), `--hold` (default 3 s), `--tol` (default 0.1 m), `--pass-tol` (default 0.2 m), `--init-ned N E D` and `--init-euler ROLL PITCH YAW` (degrees) for the initial pose, `--out DIR`, `--no-plots`. A run ends when every waypoint has been passed in order (within `--pass-tol`) and the last one has then been held within `--tol` for `--hold` seconds, at the time limit, or when roll or pitch passes 80 degrees (counted as a crash). After the flight, the recorded state lines are replayed through the same backend with `--trace`, which appends the navigator's output to every motor line; the script checks that the motor commands equal the flown ones and logs the navigator's index, position setpoint, velocity and acceleration feed-forward and heading setpoint.

The simulator is `CtrlAviary` with `DroneModel.CF2X`, `Physics.PYB` (PyBullet rigid-body dynamics, no drag, ground effect or downwash), physics at 240 Hz and control at 120 Hz, so the controller is given `dt = 1/120` s and each command is held for two physics steps. The vehicle starts at rest on the ground at the origin, facing north.

The tilted-start test used for tuning holds 1 m over the origin after starting there at roll 25, pitch -15 and yaw 30 degrees:

```
.venv/bin/python run_demo.py --backend bin --params params/cf2x.txt --params params/hover.txt \
  --init-ned 0 0 -1 --init-euler 25 -15 30 --duration 6 --hold 99 --out out/recovery
```

## Lock-step protocol and changes to `Flight/Main.lean`

Each control tick, `run_demo.py` writes one line `x y z vx vy vz roll pitch yaw p q r dt` to the controller's standard input and reads one line `m1 m2 m3 m4` back before stepping the simulator; `Main.lean` flushes standard output after every answer. Apart from the navigator and the feed-forward inputs of the position controller (see Navigation below), the control modules under `Flight/` are as before. `Flight/Main.lean` gained command-line options, so that the Crazyflie values live outside the library defaults:

- `--params FILE` (repeatable): override lines `key value...`, where the key is a dotted path into `Controller.Params` (for example `rate.roll.kd 0`, `mixer.f1 -0.5 0.5 0.5`); `waypoint N E D yaw` lines replace the built-in mission, and `mission.clear` drops waypoints read so far. Comments start with `#`.
- `--set "KEY VALUE..."`: one more override line, applied after the files.
- `--exact`: print each motor command as the exact decimal expansion of its binary64 value (finite for any binary fraction), so the text identifies the bits; without it, `Float.toString` prints six decimals. `run_demo.py` always passes `--exact`, which also hands the simulator the full-precision command.
- `--print-params`: print the effective parameters and exit; `run_demo.py` uses it to learn the mission and navigator parameters the controller will use.
- `--trace`: append the navigator's output and leg index to each motor line (logging only; the first four numbers are unchanged).

`--selftest` still runs the built-in plant (with the library defaults, or with the given overrides).

## Frames and conversions

PyBullet reports position and velocity in its world frame, ENU (x east, y north, z up), the attitude as a quaternion of the URDF body frame, FLU (x forward, y left, z up), and the angular velocity in the world frame (`getBaseVelocity`). The controller expects NED (x north, y east, z down), a forward-right-down (FRD) body frame, ZYX Euler angles, and body rates. The conversion in `enu_state_to_ned` uses two fixed proper rotations, `T = [[0,1,0],[1,0,0],[0,0,-1]]` (ENU to NED) and `D = diag(1,-1,-1)` (FRD to FLU):

- position and velocity: `p_ned = T p_enu`, that is `x_ned = y_enu`, `y_ned = x_enu`, `z_ned = -z_enu`;
- attitude: `R_ned_frd = T R_enu_flu D` from the quaternion, then roll `atan2(R32, R33)`, pitch `-asin(R31)`, yaw `atan2(R21, R11)`;
- body rates: `(p, q, r) = R_ned_frd^T T omega_enu`.

Both matrices have determinant +1, so angular velocity transforms like any vector. The conversion was checked against known poses: PyBullet roll, pitch, yaw `(0.1, 0.2, 0.3)` gives NED roll 0.1, pitch -0.2, yaw `pi/2 - 0.3`; a world angular velocity of +1 rad/s about up gives `r = -1`.

## Motor map and RPM

| Controller (`Flight/Types.lean`) | CF2X propeller (`cf2x.urdf`, FLU position) | spin seen from above |
|---|---|---|
| m1 front-right | prop0 (+x, -y) | counter-clockwise |
| m2 rear-left | prop2 (-x, +y) | counter-clockwise |
| m3 front-left | prop3 (+x, +y) | clockwise |
| m4 rear-right | prop1 (-x, -y) | clockwise |

The spin directions of the simulator follow from its yaw torque `-t0 + t1 - t2 + t3` about body up: propellers 0 and 2 push the body clockwise, so they spin counter-clockwise. A short open-loop test (positive roll, pitch and yaw torque commands through the controller's mixer factors) produced positive p, q and r respectively.

A motor command `m` in [0, 1] is a fraction of the maximum per-motor thrust `T_max = kf MAX_RPM^2`, so `rpm = sqrt(m T_max / kf) = MAX_RPM sqrt(m)`, clipped to [0, MAX_RPM]. The URDF gives mass 0.027 kg, `kf = 3.16e-10`, `km = 7.94e-12`, arm 0.0397 m, thrust-to-weight 2.25; the environment derives `MAX_RPM = 21702.6` and uses gravity 9.8. With this map, hover is `m = 1/2.25 = 0.444`.

## Navigation (`Flight/Navigator.lean`)

The navigator follows `AC_WPNav` in a reduced form. It sends the vehicle to the first waypoint as a position step (take-off), and once within `nav.acceptRadius` of it moves a target along straight legs through the remaining waypoints, rounding every inner corner by a quadratic Bezier blend of radius `nav.cornerRadius` (at most half the shorter leg). The target's path speed follows a trapezoidal profile: it accelerates at `nav.wpAccel` to `nav.wpSpeed` and brakes at `nav.wpAccel` to the corner speed, the largest speed at which the blend's constant acceleration `v^2 |d2 - d1| / (2 r)` stays within `nav.wpAccel`, and to rest at the last waypoint, where it then holds. The navigator outputs the target position, its velocity and its acceleration; the position controller adds the velocity to its proportional correction and the acceleration to its velocity-PID output, as `AC_PosControl` does with the navigator's feed-forward (without the acceleration term the vehicle lagged the target by up to 32 cm after each corner; with it, by at most 5.2 cm). With `nav.yawAlongPath 1` the heading setpoint is the direction of the path tangent; with `0` it is the yaw stored with the waypoint being flown to, as before. The module header lists the departures from ArduCopter.

## Tuned parameters (`params/cf2x.txt`, `params/cf2x-course.txt`)

The course (`cf2x-course.txt`, passed after `cf2x.txt`) is a figure eight of two diamonds with 1.25 m half-diagonal that meet over the origin, eight waypoints from `(0, 0, -0.8)` through `(1.25, 1.25, -1.0)`, `(0, 2.5, -1.2)`, `(-1.25, 1.25, -1.4)`, the leg back through the crossing to `(1.25, -1.25, -1.6)`, then `(0, -2.5, -1.4)`, `(-1.25, -1.25, -1.1)` and back to `(0, 0, -0.8)` (NED): the first lobe turns left and climbs, the second turns right and descends, 13.8 m in all. It sets path speed 1 m/s, path acceleration 1.5 m/s^2, blend radius 0.3 m, heading along the path, and raises the horizontal speed limit to 1.5 m/s so the correction has room above the 1 m/s feed-forward.

The corner mission of `cf2x.txt` is the built-in one scaled down: climb to 1 m, fly 2 m north, then 2 m east while turning to face east (waypoints `(0,0,-1,0)`, `(2,0,-1,0)`, `(2,2,-1,pi/2)`, acceptance radius 0.05 m, the same path speed, acceleration and blend radius as the course, heading from the waypoints). Changes from the library defaults: hover throttle 0.4444 and gravity 9.8 (thrust model above); lean limit 20 degrees; roll and pitch rate `kd` 0 (default 0.0036); roll and pitch angle gains 8 (default 4.5); vertical position gain 1.5; horizontal velocity PID `kp` 3, `ki` 0.5 (defaults 2, 1); speed limits 1 m/s; acceleration limits 3 m/s^2. Every field is listed in the file, defaults included.

Tuning went bottom-up with the tilted-start test, then the mission. The one structural problem was the rate-loop derivative: with the CF2X inertia, a unit of normalized roll torque gives about 595 rad/s^2, so the derivative term `kd (e_k - e_{k-1}) / dt` changes the rate by `595 kd` per unit change of error each tick; at the default `kd = 0.0036` that factor is 2.1 and the discrete loop has a root outside the unit circle. In simulation `kd = 0.002` oscillates and the default `kd = 0.0036` flips the vehicle within 2.4 s (`out/default-rate-kd/`); `kd` of 0 or 0.001 is clean. No sign error between frames and no mixer mismatch was found. The rate proportional gain is uncritical between 0.06 and 0.3; higher angle gains shorten the recovery from a tilt (3 to 14 tried; 8 chosen). With the default horizontal velocity PID (`kp` 2, `ki` 1) the vehicle drifted back out to 14.4 cm from the last waypoint after first entering the 0.1 m sphere; `kp` 3, `ki` 0.5 keeps it inside once reached.

## Results

The figure-eight course; all three backends fly the identical trajectory (from `out/*/summary.txt`):

- ends after 19.83 s of simulated time (2381 ticks) with the last waypoint held 3 s within 0.1 m; final error 0.22 cm, final yaw 45.00 degrees (the heading of the last leg);
- max |roll| 9.8 degrees, max |pitch| 10.8 degrees, max tilt 10.8 degrees (lean limit 20);
- on the path, the vehicle stays within 5.2 cm of the navigator's position setpoint (rms 2.7 cm); top speed 1.13 m/s;
- the legs toward waypoints 1 to 7 start at 1.28, 3.48, 5.43, 7.38, 11.10, 13.06 and 15.03 s; the closest approach to waypoints 1 to 6 is 6.6 to 8.0 cm (the blend rounds each corner inside the waypoint by design), and the vehicle is within 0.1 m of the last waypoint at 16.83 s;
- round trip per tick: median 137 us for `lake`, 140 us for `bin`, 399 us for `interp`; batch cost per line with `--exact` 129 us (`lake`), 128 us (`bin`), 407 us (`interp`).

The corner mission (`--params params/cf2x.txt`) now ends after 8.9 s with final error 0.45 cm, max tilt 11.1 degrees, and the vehicle within 5.2 cm of the setpoint on the path. The tilted-start test (`out/recovery/`) is unchanged by the new navigator (it never leaves the take-off step with one waypoint): roll, pitch and yaw come back to level and north within about 1 s, with at most 15 cm of drift, and the point is held to 1.6 cm after 6 s.

## Determinism

`run_demo.py --determinism` flies the mission with each backend from the same initial state and compares the motor lines (exact decimal expansions, so equal text means equal bits); it then replays the state lines recorded in the `lake` run through every backend in one batch and compares again. Result for the course (`out/determinism.txt`): closed loop, `lake` vs `bin` 0 of 2381 lines differ and `lake` vs `interp` 0 of 2381; replay, 0 differ for both. The interpreter gives the same bits because the Float operations it calls are the same compiled runtime functions.

## Output files

For each run, in `out/<backend>/` (or `--out`):

- `flight.csv`: one row per tick with `t`, NED position `x_n y_e z_d`, velocity `vx_n vy_e vz_d`, Euler `roll pitch yaw` (rad), body rates `p q r` (rad/s), motor commands `m1..m4`, the navigator's output from the `--trace` replay (`nav_index`, position setpoint `sp_n sp_e sp_d`, velocity feed-forward `vsp_n vsp_e vsp_d`, acceleration feed-forward `asp_n asp_e asp_d`, heading setpoint `sp_yaw`), and the round trip `tick_us`;
- `inputs.txt`, `motors.txt`: the raw lines sent to and received from the controller;
- `summary.txt`: the printed summary;
- `timeseries.png`: position with setpoints, roll and pitch, yaw with setpoint, motor commands;
- `path.png`: top-down path with setpoint and waypoints, and altitude and horizontal range against time.

`out/determinism.txt` holds the comparison, `out/recovery/` the tilted-start test, `out/default-rate-kd/` the failing run with the default rate `kd`, and `out/strobe/` the time lapse of `render_strobe.py`. `out/corner/` keeps the runs of the corner mission made with the earlier navigator, which jumped the setpoint from waypoint to waypoint; they cannot be reproduced with the current code.

## Limitations

The navigator's speed profile has no jerk limit, so the acceleration feed-forward steps where the profile switches between accelerating, cruising and braking and where a blend begins or ends; each step shows as a short spike in the motor commands. Corners are cut by the blend (6.6 to 8.0 cm inside the waypoints on the course), there is no loiter time at inner waypoints, and the target does not wait for a vehicle that falls behind (on the course the vehicle never lags by more than 5.2 cm). The heading lags its setpoint through the corners because the yaw rate is limited to 1.57 rad/s. The angle loop uses Euler-angle errors as body-rate errors and the vertical channel uses a fixed hover throttle, as documented in the control modules; both are adequate at the tilts flown here (under 11 degrees). The simulator state is exact (no sensor noise, delay or motor dynamics) and `Physics.PYB` omits drag, ground effect and downwash. Every gain the tuning needed could be expressed through `Params`.

## The copter driver (`run_copter.py`)

`run_copter.py` flies `copter`, the Lean port of ArduCopter (`../Copter/Main.lean`), which replaces `flight`. It keeps the structure of `run_demo.py` (lock-step pipes, three backends, `--exact`, the `--trace` replay, `--determinism`, `summary.txt` and plots) and changes the rates, the input line, the motor map and the parameter files.

- `lake`: `lake exe copter`; `bin`: `build/copter-c`, built by `build_copter_c.sh`; `interp`: `lake env lean --run Copter/Main.lean`; `stub`: a stand-in controller built into `run_copter.py` (`--stub-controller`), which reads the protocol and answers constant actuators (hover, plus optional open-loop roll, pitch, yaw and throttle offsets `--stub-rpyt R P Y T` through the quad X factors), for testing the driver without Lean.
- Rates: control at 400 Hz (ArduCopter's main loop), physics at 1200 Hz (`--pyb-hz`, 800 also accepted; CtrlAviary needs a multiple of the control rate), so `dt = 0.0025` s and each command is held for three physics steps.

```
.venv/bin/python run_copter.py --check-frames                      # conversion and motor-map checks
.venv/bin/python run_copter.py --backend stub --params params/copter-cf2x.txt --params params/copter-hover.txt
.venv/bin/python run_copter.py --determinism --params params/copter-cf2x.txt --params params/copter-hover.txt \
  --duration 10 --hold 99 --out out/copter-hover                   # hover test, all three backends
.venv/bin/python run_copter.py --determinism --duration 30 --out out/copter-course   # figure-eight course
.venv/bin/python run_copter.py --determinism --params params/copter-cf2x.txt \
  --params params/copter-course-speed.txt --duration 60 --out out/copter-course-1ms  # the course at 1 m/s
```

Options are those of `run_demo.py` (`--params`, `--set`, `--duration`, `--hold`, `--tol`, `--pass-tol`, `--init-ned`, `--init-euler`, `--gui`, `--out`, `--no-plots`, `--determinism`) plus `--pyb-hz`, `--ground-timeout` (default 3 s: the run ends if the vehicle is still, or again, on the ground after that), `--no-trace` and `--no-exact`. Outputs go to `out/copter-<backend>/` and `out/copter-determinism.txt`. The mission for the end condition and the summary is read from the controller's `--print-params` (lines `waypoint N E D`) when it supports the option, otherwise from the parameter files.

### Protocol

One input line per control tick, 17 numbers: `x y z vx vy vz ax ay az q1 q2 q3 q4 p q r dt`.

- `x y z`, `vx vy vz`: NED position (m) and velocity (m/s), from `enu_state_to_ned` unchanged. The NED origin is the PyBullet world origin on the ground plane; the vehicle rests with its base at `z = -0.0135`.
- `ax ay az`: the earth-frame specific force in NED, as `AP_AHRS::get_accel_ef` returns it: the vehicle's true NED acceleration minus the gravity vector `(0, 0, +9.80665)`, so `(0, 0, -9.80665)` at rest and `(0, 0, 0)` in free fall. The acceleration is the backward difference of the NED velocity over the last control period, `(v_k - v_{k-1}) / dt`, which equals the mean of the accelerations of its three physics substeps (the differences telescope). It is therefore the mean over the tick during which the previous command was applied, half a tick behind the instantaneous value. On the first tick there is no previous velocity: the vehicle starts at rest with no thrust yet, so the value is `(0, 0, -9.80665)` on the ground and `(0, 0, 0)` for an airborne start.
- `q1 q2 q3 q4`: the attitude quaternion in ArduPilot's convention (`q1` scalar, rotating FRD body vectors into NED), computed as the quaternion product `q(T) * q_enu_flu * q(D)` with `q(T) = (0, 1/sqrt2, 1/sqrt2, 0)` (the half turn about the north-east bisector, the matrix `T` above) and `q(D) = (0, 1, 0, 0)` (the half turn about forward, `D` above): the quaternion form of `R_ned_frd = T R_enu_flu D`. It is normalized and its sign chosen with `q1 >= 0`. Level and facing north is `(1, 0, 0, 0)`.
- `p q r`: body rates about FRD (rad/s), as before; `dt`: 0.0025.

Output line: `m1 m2 m3 m4`, the actuator outputs in [0, 1] of ArduPilot motor slots 0..3 of the quad X frame (`AP_MotorsMatrix::setup_quad_matrix`, `MOTOR_FRAME_TYPE_X`); with `--trace`, further fields follow, which the driver stores as `trace0, trace1, ...` in `flight.csv` and in `trace.txt` after checking that the first four equal the flown ones.

### Motor map (ArduPilot quad X)

| ArduPilot slot (angle from the nose, clockwise positive) | CF2X propeller (`cf2x.urdf`, FLU position) | spin seen from above |
|---|---|---|
| 0 at 45 deg, front-right | prop0 (+x, -y) | counter-clockwise |
| 1 at -135 deg, rear-left | prop2 (-x, +y) | counter-clockwise |
| 2 at -45 deg, front-left | prop3 (+x, +y) | clockwise |
| 3 at 135 deg, rear-right | prop1 (-x, -y) | clockwise |

This is the order of the `flight` controller's `m1..m4`, so the propeller assignment `SLOT_TO_SIM = [0, 2, 3, 1]` is unchanged; spin directions as in "Motor map and RPM" above.

An actuator value `a` is taken as the thrust fraction: `rpm = MAX_RPM sqrt(a)`, clipped. In AP_Motors the actuator is the ESC command, and the thrust it produces is the thrust curve of the ESC and motor (`MOT_THST_EXPO`, `MOT_SPIN_MIN`, `MOT_SPIN_MAX`), which the simulator does not model. With `MOT_THST_EXPO 0`, `MOT_SPIN_MIN 0` and `MOT_SPIN_MAX 1` the Lean side's `actuator_to_thrust` is the identity, so the actuator it outputs is the thrust fraction it intends; `params/copter-cf2x.txt` sets these values for the first flights. With any other values, the simulated thrust would not be the thrust the controller linearized for.

### Simulator changes from `run_demo.py`

- Gravity is ArduPilot's `GRAVITY_MSS = 9.80665` instead of the environment's 9.8 (`env.G`, with `GRAVITY`, `HOVER_RPM`, `MAX_RPM` and `MAX_THRUST` recomputed as `BaseAviary.__init__` does), so the thrust-to-weight ratio stays 2.25 and hover is the thrust fraction `1/2.25`, matching `MOT_THST_HOVER 0.4444`.
- PyBullet's default velocity damping (0.04 linear and angular, a drag-like term the URDF does not ask for) is set to zero with `changeDynamics`; with it, the specific force in free fall was `-0.04 v` instead of zero. The vehicle is now the rigid body of the thrust and drag-torque model only.
- A vehicle that starts on the ground is first stepped for 0.25 s with the motors off: the URDF base overlaps the ground plane slightly and the contact pushes it out over the first 20 or so ticks, with specific-force transients up to 40 m/s^2. The run's clock starts after that.

### Validation (`--check-frames`, `out/copter-frames.txt`)

- Quaternion against the Euler angles of `enu_state_to_ned`, for 20000 random PyBullet attitudes (|pitch| < 1.5 rad): ArduPilot's `Quaternion::to_euler` of the quaternion differs from them by at most 7.6e-15 rad, and its `rotation_matrix` from `T R_enu_flu D` by at most 1.3e-15. Known poses: PyBullet roll, pitch, yaw `(0.1, 0.2, 0.3)` gives `q = (0.796853, 0.099201, -0.050735, 0.593811)`, whose `to_euler` is `(0.1, -0.2, pi/2 - 0.3)` as for the earlier conversion; facing north gives `(1, 0, 0, 0)`; facing east gives `(cos 45, 0, 0, sin 45)`, a quarter turn about down.
- Specific force at rest on the ground, motors off, 1 s: the first tick is exactly `0.0 0.0 -9.80665`; on later ticks the contact jitters by at most 0.012 m/s^2, and the mean is `(-7e-10, 1e-9, -9.806650)`.
- Free fall from 3 m, motors off, 0.5 s: |f| at most 5e-13 m/s^2, and the vertical speed after 199 ticks is `g t` to 6 digits.
- Hover actuators `1/2.25` at 1 m: `f = (0, 0, -9.80665)` to 4e-15 and the altitude unchanged to 1e-9 after 1 s; tilted start (roll 20, pitch -10, yaw 30 degrees) with hover actuators: `f = R(q) (0, 0, -g)` to 9e-15, so the specific force points along body up as rotated by the reported quaternion.
- Lift-off with all actuators at 0.4944: `f_z = -0.4944 * 2.25 * 9.80665 = -10.9099` to 5e-7 from the second tick on.
- Motor map, open loop from a level hover at 2 m, actuators `hover + input * factor` with the normalized quad X factors of `AP_MotorsMatrix` (roll `cos(angle + 90)`, pitch `cos(angle)`, scaled to 0.5; yaw +0.5 for counter-clockwise and -0.5 for clockwise slots): roll input +0.02 gives `p = +1.16 rad/s` and roll +3.27 degrees after 0.1 s with `q`, `r` zero; pitch +0.02 gives `q = +1.16 rad/s` and pitch +3.27 degrees; yaw +0.05 gives `r = +1.68 rad/s` and yaw +4.74 degrees. Positive inputs move the vehicle in the positive NED roll, pitch and yaw senses (right side down, nose up, nose right).

### Parameter files

`params/copter-cf2x.txt` uses the ArduPilot parameter names, one `NAME value` per line, and sets only `MOT_THST_EXPO 0`, `MOT_SPIN_MIN 0`, `MOT_SPIN_MAX 1`, `MOT_BAT_VOLT_MAX 0`, `MOT_HOVER_LEARN 0` and `MOT_THST_HOVER 0.4444`; every other parameter keeps the ArduPilot default. Its mission is the figure-eight course of `cf2x-course.txt` as `waypoint N E D` lines (NED meters, no yaw: ArduCopter's Auto mode sets the heading itself, `WP_YAW_BEHAVIOR 2`). `params/copter-hover.txt`, passed after it, replaces the mission by the single waypoint `(0, 0, -1)` (`mission.clear`). `params/copter-course-speed.txt`, passed after it, sets the path speed and acceleration of the earlier course flights, `WP_SPD 1` and `WP_ACC 1.5` (ArduPilot defaults 10 m/s and 2.5 m/s^2); all gains stay at the ArduPilot defaults in every run below. `copter` assumes the vehicle armed and hovering when the first line arrives (`run.start_hover 1`, see `Copter/Loop.lean`) and enters Auto on that tick; the vehicle here starts on the ground, so the first tick's throttle is the hover throttle and it lifts off.

### The C route (`build_copter_c.sh`)

As `build_c.sh`, for the `copter` target: `lake build copter`, then the import closure of `Copter.Main` is collected from the `import` lines of the sources (Init, Std and Lean are left out; their code is in the toolchain's static archives), the emitted C files are copied to `build/copter-c.d/`, compiled with `leanc -c -O3 -DNDEBUG` and linked into `build/copter-c`. Checked on `Flight.Main`, where it finds the same thirteen modules that `build_c.sh` lists.

### Flights (Lean at commit 8af1a50, physics 1200 Hz, control 400 Hz, ArduPilot default gains)

Hover (`out/copter-hover/`, 10 s): the vehicle climbs at up to 1.04 m/s, is within 0.1 m of the waypoint at 1.49 s, overshoots to 1.114 m (the vertical position leads AC_PosControl's target by up to 11.7 cm during the climb), and settles at 1.0569 m with tilt under 0.05 degrees. The settled point is not the waypoint: when `AC_WPNav` reports the waypoint reached (`WP_RADIUS_M` defaults to 2 m), the mission is complete and `ModeAuto::exit_mission` calls `loiter_start`, which moves the target to the stopping point computed from the vehicle's position and velocity at that tick, 5.69 cm above the waypoint. Distance to the position target: max 11.69 cm, rms 3.36 cm.

Figure-eight course with the ArduPilot defaults (`out/copter-course/`, 30 s): `WP_SPD 10`, `WP_ACC 2.5` and the default corner acceleration (`WP_ACC_CNR 0`, so twice `WP_ACC`) give a target that reaches 2.98 m/s and 5.6 m/s^2 on legs of 1.8 m. The vehicle saturates at the 30 degree lean limit (`ATC_ANGLE_MAX`; max tilt 32.4 degrees, max roll 29.9, max pitch 29.6), lags the target by up to 94 cm (rms 30 cm), and swings up to about 0.6 m outside the target's rounded corners; it passes within 0.2 m of waypoints 0 to 6 in order (closest 6.0 to 17.1 cm) but not of the last one (closest 27.7 cm at 9.17 s). The mission completes at about 9 s and the vehicle loiters at the stopping point `(0.701, -0.110, -0.781)`, 71.0 cm from the last waypoint, until the time limit; it never crashes, and the attitude follows its target within 2.3 degrees.

Figure-eight course at 1 m/s (`out/copter-course-1ms/`, `copter-course-speed.txt`): ends after 21.08 s (8431 ticks) with the last waypoint held 3 s within 0.1 m; final error 7.89 cm (again the loiter stopping point); max roll 16.7, pitch 12.4, tilt 17.5 degrees; top speed 1.45 m/s against a target speed of at most 1.01 m/s; distance to the position target max 22.0 cm, rms 12.3 cm; closest approach to waypoints 0 to 7: 0.8, 2.8, 10.8, 12.5, 5.7, 8.1, 11.7, 4.2 cm. The vehicle swings outside the target's corners by up to about 15 cm.

Timing (wall clock per simulated second, whole flight loop including the controller's start-up): `lake` 0.15 s for the 30 s course (start-up 1.7 s, then about 0.08 s), `bin` 0.087 s, `interp` 0.39 s; physics at 1200 Hz costs 0.013 s per simulated second, the controller round trips 0.065 s (`lake`, `bin`, median 160 us per tick) and 0.29 s (`interp`, 735 us). Batch cost per tick with `--exact`: 152 us (`lake`), 151 us (`bin`), 754 us (`interp`).

### Determinism: the compiled routes differ from the interpreter

`lake` and `bin` are identical bit for bit in every run (closed loop and replay: 0 of 4000, 12000 and 8431 lines differ), and the replay of the live `lake` inputs reproduces the live run. The interpreter is not identical: on the hover replay 7 of 4000 actuator lines differ (first at line 1066; in the trace, the pitch-rate target differs by one `float` ulp from line 908), on the course 11379 of 12000 (first at line 620) and on the 1 m/s course 7076 of 8431 (first at line 503); in closed loop the trajectories then diverge slowly (final positions equal to 1 mm on the 30 s course). The cause is clang's library-call fusion, not Lean: at `-O3`, clang replaces a `sinf(x)` and a `cosf(x)` of the same argument in one function by one call of Apple's `__sincosf_stret` (`nm -u` lists it for `.lake/build/bin/copter` and `build/copter-c`, from `AP_Math/quaternion`, `AC_AttitudeControl` and `AC_PosControl`), and `__sincosf_stret` is not bit-identical to `sinf`/`cosf`: over all floats in [-7, 7] its sine differs on 2157922 of 213506851 values and its cosine on 964600. The interpreter calls `sinf` and `cosf` separately. With the fusion disabled (`EXTRA_CFLAGS="-fno-builtin-sinf -fno-builtin-cosf" BIN=build/copter-c-nosincos ./build_copter_c.sh`) the binary is bit-identical to the interpreter on all three replays (0 lines differ). The `flight` executable (binary64) also links the double version `__sincos_stret`, and its three routes were identical; whether that version always agrees with `sin`/`cos` was not checked here. Making all three routes agree needs the same flags on lake's compile of the `Copter` modules (`moreLeancArgs` in the lakefile), or a port that does not let the C compiler pair the calls.

## Tuning (`params/copter-cf2x-tuned.txt`)

The flights above use ArduPilot's default gains. `params/copter-cf2x-tuned.txt` is a parameter overlay that tunes them for the CF2X on the 1 m/s figure-eight. It changes parameters only: no Lean file and no driver code. Pass it after the course files:

```
.venv/bin/python run_copter.py --backend bin --params params/copter-cf2x.txt \
  --params params/copter-course-speed.txt --params params/copter-cf2x-tuned.txt --duration 60 --out out/copter-tune-final
```

The vertical channel was left at the values the hover proof uses (`PSC_D_POS_P`, `PSC_D_VEL_*`, `PSC_D_ACC_*`, `MOT_THST_HOVER`, the throttle filter and the linear `MOT_*` configuration of `copter-cf2x.txt`), and every value is inside the `@Range` of ArduPilot's parameter metadata (`AC_PosControl.cpp`, `AC_AttitudeControl.cpp`, `AC_AttitudeControl_Multi.cpp`, `AC_WPNav.cpp`). The course itself (`WP_SPD 1`, `WP_ACC 1.5` of `copter-course-speed.txt`) was not changed.

### Method

One group at a time, roughly in the order an ArduPilot tuner works: horizontal position and velocity gains, attitude angle gains, rate PIDs, input shaping, navigator, then margin probes and an ablation of the result. Each run is the `bin` backend on the 1 m/s course with a 60 s limit (`out/copter-tune-<run>/`, with the overlay used in `overlay.txt`). The figures recorded per run are the tracking error from `summary.txt` (the distance to AC_PosControl's position target, max and rms over the whole run), its horizontal part (from `flight.csv`), the max tilt, the final error to the last waypoint and how the run ended. A setting was rejected if it tilted the vehicle past 25 degrees or oscillated. Oscillation was checked in `flight.csv`: the 8 Hz high-passed body rates per second of flight (to catch rate-loop ringing) and the tilt envelope per second after the target stops (to catch a velocity-loop limit cycle). A run that ends on the time limit has an rms averaged over 60 s, mostly hover, so its rms is not comparable with the others; its max is.

### What each group did

- `PSC_NE_POS_P` alone, on the default gains, made tracking worse: 1.5 to 4 raised the max error from 22.0 cm to between 22.9 cm (1.5) and 38.2 cm (4), and from 1.5 to 3 the run never held the last waypoint (the loiter point ended 11 to 19 cm away). With the default velocity loop (`PSC_NE_VEL_P 2`) and attitude shaping, the position loop cannot be stiffer than the loop inside it. AC_WPNav's track-speed scaler (which slows the target in proportion to `PSC_NE_POS_P` times the along-track error) makes the target speed swing with it.
- `ATC_INPUT_TC` gave the largest single gain. On the course, every phase change of SimplePath's trapezoid steps the acceleration feed-forward, by up to 2.1 m/s^2 in the 90 degree corners, so the lean target steps by about 12 degrees. With the default 0.1 s, the shaped attitude target takes about 0.3 s to follow, and the vehicle falls 20 cm behind in each corner. 0.05 s (the "Very Crisp" end of the documented values) took the max error from 22.0 to 12.4 cm. With it, the shaping's acceleration limit binds, so `ATC_ACC_R_MAX`/`ATC_ACC_P_MAX` 1800 (the top of the range; default 1100) adds a little more. 0.03 and 0.02 go further (H max 8.7 and 8.1 cm instead of 11.0) but are below any documented value and raise the rate transients in the corners by half to nearly double, so they were not adopted.
- `ATC_ANG_RLL_P`/`ATC_ANG_PIT_P`: 6 to 12 change the default-gain flight by at most 0.3 cm. In the tuned set, 9 instead of 4.5 cuts the largest pitch error behind the shaped target from 4.4 to 2.4 degrees, the horizontal max from 6.7 to 4.5 cm and the final error from 3.5 to 2.4 cm. 12 adds nothing measurable.
- `PSC_NE_VEL_P` gave the second largest gain: on the fast attitude loop, 2 to 6 took the rms from 6.2 to 3.5 cm. `PSC_NE_VEL_D` 0.5 (default 0.25) damps the overshoot after the corners and at the last waypoint. `PSC_NE_VEL_I` 0.5 or 2 changes nothing beyond noise, so it stays at 1. The velocity loop has a clear stability edge, a 1.4 Hz swing that grows to the 30 degree lean limit (`B2velp8d0.75`, `E1_velp9`, `E1_veld1.25`). With the tuned set it oscillates from `PSC_NE_VEL_P` 9 (D 0.5) or 10 (D 0.25), and from `PSC_NE_VEL_D` 1.25; D 1.0 already reaches 30 degrees in the corners. P 6 and D 0.5 leave a gain margin of 1.5 on P and 2.5 on D. Higher P lowers the error further (P 8: rms 2.58 cm) but at a 1.1 margin.
- `PSC_NE_POS_P` on the tuned inner loops: 1.5 now helps a little (H max 4.8 to 4.5 cm). At 3 the tilt reaches 23 degrees with large swings in the final hold, and at 4 it reaches 29.6 degrees.
- Rate PIDs (`ATC_RAT_RLL_*`, `ATC_RAT_PIT_*`): the tracking is insensitive to them. P 0.09 to 0.2 and D 0 to 0.01 change the rms by under 0.1 cm, and none rings. The derivative problem of the earlier stack (above) does not appear here: ArduPilot's rate loop runs at 400 Hz and filters the derivative at `ATC_RAT_*_FLTD` 20 Hz, where the `flight` controller ran at 120 Hz with an unfiltered difference. The rate PIDs stay at the ArduPilot defaults, including `D` 0.0036.
- `WP_RADIUS_M`: on the course, 0.3, 0.5 and 1 give motor commands bit-identical to the default 2. At 0.1 the last waypoint counts as reached only once the vehicle is within 10 cm, and `ModeAuto::exit_mission` then takes the loiter target from the vehicle's position and velocity at that tick (`get_stopping_point_NE_m`). On the default gains this made the end worse: the vehicle swung through the waypoint at 0.5 m/s and the loiter point landed 36.7 cm away (`rad0.1`). With the tuned gains the vehicle arrives slowly, and 0.1 gives a final error of 2.4 cm instead of 2.6 cm and a slightly lower rms (2.82 instead of 2.99 cm), so 0.1 is kept.
- `WP_JERK`: SimplePath does not read it. Its only effect in this port is the time constant `WP_ACC / WP_JERK` of AC_WPNav's track-speed scaler, which is ported line for line from the C++. 5 (default 1) shortens that time constant from 1.5 s to 0.3 s, and the largest change is on the take-off climb, where the vertical error falls from 11.0 to 9.5 cm.
- No effect or rejected: `PSC_NE_JERK` 20 gives bit-identical motor commands: on this course it would only limit the jerk of a change in the navigator's commanded speed (`_offset_vel_ms`), and that speed never changes. `WP_ACC_CNR` 2, below the 2.12 m/s^2 the 90 degree blends need, turns every corner into a stop (rms 6.5 cm, 5 s longer). `ATC_ANGLE_MAX` stays at 30 degrees because the tilt never saturates at 1 m/s (max 21.4 degrees). `WP_ACC 1` would cut the rms to 2.25 cm and the tilt to 13.4 degrees, but it changes the course, so it is not part of the overlay.

Ablation: each group put back to its default in the tuned set (max / rms tracking error, horizontal max):

| put back to default | tracking max / rms (cm) | horizontal max (cm) | max tilt (deg) | final error (cm) |
|---|---|---|---|---|
| none (tuned set) | 9.86 / 2.82 | 4.53 | 21.4 | 2.41 |
| `ATC_INPUT_TC` 0.1 | 13.62 / 3.26 | 13.62 | 23.0 | 15.77 (no hold) |
| `ATC_ACC_R/P_MAX` 1100 | 9.92 / 3.17 | 5.58 | 22.7 | 2.56 |
| `ATC_ANG_RLL/PIT_P` 4.5 | 9.84 / 3.01 | 6.73 | 23.2 | 3.52 |
| `PSC_NE_POS_P` 1 | 9.99 / 2.91 | 4.83 | 21.0 | 2.41 |
| `PSC_NE_VEL_P` 2, `D` 0.25 | 11.51 / 5.45 | 9.37 | 16.8 | 2.51 |
| `WP_RADIUS_M` 2 | 9.86 / 2.99 | 4.54 | 21.8 | 2.58 |
| `WP_JERK` 1 | 11.01 / 3.22 | 5.38 | 21.4 | 2.17 |

### Result

The 1 m/s figure-eight, default gains (`out/copter-tune-baseline/`, identical to `out/copter-course-1ms-det/copter-bin/`) against the tuned set (`out/copter-tune-final/`, with plots):

| | default gains | tuned |
|---|---|---|
| tracking error to the position target, max / rms | 22.04 / 12.29 cm | 9.86 / 2.82 cm |
| horizontal part, max / rms | 22.01 / 12.09 cm | 4.53 / 2.00 cm |
| vertical part, max (take-off climb) | 10.83 cm | 9.53 cm |
| max tilt (roll, pitch) | 17.5 deg (16.7, 12.4) | 21.4 deg (17.4, 15.5) |
| max attitude error behind its target (roll, pitch) | 1.23, 1.26 deg | 1.69, 2.40 deg |
| max speed (target 1.01 m/s) | 1.454 m/s | 1.199 m/s |
| closest approach to waypoints 0..7 | 0.8, 2.8, 10.8, 12.5, 5.7, 8.1, 11.7, 4.2 cm | 2.4, 6.0, 5.6, 5.7, 5.5, 5.9, 5.7, 0.9 cm |
| end | last waypoint held 3 s at 21.08 s | last waypoint held 3 s at 18.97 s |
| final error to the last waypoint | 7.89 cm | 2.41 cm |
| max distance from the last waypoint after first reaching it | 11.95 cm | 6.00 cm |

The max tracking error is now set by the vertical channel during the take-off climb (the vehicle leads the climbing target by up to 9.5 cm at about 1.8 s, as in the hover test), which the overlay does not touch. The horizontal error that remains (4.5 cm) comes from the stepped acceleration feed-forward of SimplePath meeting the attitude acceleration limit at the top of its range; ArduPilot's SCurve, which is not ported, would ramp that acceleration at `WP_JERK`. The vehicle no longer swings outside the corners: the closest approaches to the inner waypoints are all about 5.7 cm, which is the target's own blend, cut inside the corner by design. The rate and motor traces (`timeseries.png`) are active only at the feed-forward steps, are quiet on the straight legs and in the hold, and the actuators stay within 0.369 to 0.498.

Hover test (`out/copter-tune-final-hover/`; `copter-cf2x.txt`, `copter-hover.txt`, the overlay, 10 s, against `out/copter-tune-hover-baseline/`): the vertical response is unchanged (max altitude 1.115 m against 1.114 m, tracking max 11.68 against 11.69 cm, rms 3.62 against 3.36 cm), tilt stays under 0.03 degrees, and the hover is steady. The settled point moves from 5.69 cm above to 4.43 cm below the waypoint: with `WP_RADIUS_M 0.1` the mission completes only once the vehicle falls back within 10 cm after the climb overshoot, while it is descending, so the loiter stopping point lies below the waypoint.

ArduPilot's default speed (`WP_SPD 10`, `WP_ACC 2.5`; `copter-cf2x.txt` and the overlay, no `copter-course-speed.txt`, 30 s; `out/copter-tune-final-wpspd10/` against `out/copter-tune-baseline-wpspd10/`), not tuned for: the target again reaches 2.98 m/s, and the lean saturates at the 30 degree `ATC_ANGLE_MAX` (max tilt 32.5 degrees, as with the default gains). The tracking error drops from 93.95 / 30.06 cm to 26.00 / 8.20 cm (max / rms). All 8 waypoints are passed within 0.2 m in order, against 7 of 8, with closest approaches 0.1 to 4.1 cm. The end is still the loiter jump: the vehicle enters the 10 cm sphere of the last waypoint at 10.68 s still moving, the stopping point is taken from that velocity, and the vehicle settles 19.3 cm from the waypoint (71.0 cm with the default gains). The run ends on the time limit without a hold.

Determinism (`out/copter-tune-final-det/copter-determinism.txt`, `--determinism` with the tuned overlay): closed loop, `lake` vs `bin` and `lake` vs `interp` 0 of 7586 actuator lines differ; replay of the `lake` inputs, 0 differ for both; replay vs the live `lake` run, 0 differ. The `bin` flight of that run is identical to `out/copter-tune-final/`.

### Every run

Bases: `defaults` = `copter-cf2x.txt` + `copter-course-speed.txt`; `B1` = defaults + `ATC_INPUT_TC 0.05`, `ATC_ACC_R_MAX`/`ATC_ACC_P_MAX 1800`; `B2` = B1 + `PSC_NE_VEL_P 6`, `PSC_NE_VEL_D 0.5`, `WP_RADIUS_M 0.1`; `C` = B2 + `ATC_ANG_RLL_P`/`ATC_ANG_PIT_P 9`; `D` = C + `WP_JERK 3`; `tuned` = D + `PSC_NE_POS_P 1.5`, `WP_JERK 5` (the overlay). Tracking error is to AC_PosControl's position target, from `summary.txt`.

| run | base | change | tracking max / rms (cm) | horizontal max (cm) | max tilt (deg) | final error (cm) | outcome |
|---|---|---|---|---|---|---|---|
| baseline | defaults | none (copter-cf2x + copter-course-speed) | 22.04 / 12.29 | 22.01 | 17.5 | 7.89 | held, 21.08 s |
| pos1.5 | defaults | PSC_NE_POS_P 1.5 | 22.94 / 7.86 | 22.93 | 18.2 | 11.49 | no hold: loiter point 11.5 cm from the last waypoint (60 s limit) |
| pos2 | defaults | PSC_NE_POS_P 2 | 29.08 / 9.08 | 29.08 | 18.7 | 16.73 | no hold: loiter point 16.7 cm from the last waypoint (60 s limit) |
| pos2.5 | defaults | PSC_NE_POS_P 2.5 | 35.99 / 10.02 | 35.98 | 18.9 | 18.91 | no hold: loiter point 18.9 cm from the last waypoint (60 s limit) |
| pos3 | defaults | PSC_NE_POS_P 3 | 37.35 / 10.07 | 37.32 | 18.6 | 14.86 | no hold: loiter point 14.9 cm from the last waypoint (60 s limit) |
| pos4 | defaults | PSC_NE_POS_P 4 | 38.21 / 13.21 | 38.02 | 19.8 | 8.78 | held, 33.51 s |
| ang6 | defaults | ATC_ANG_RLL_P, ATC_ANG_PIT_P 6 | 22.00 / 12.15 | 21.97 | 17.4 | 7.69 | held, 21.05 s |
| ang9 | defaults | ATC_ANG_RLL_P, ATC_ANG_PIT_P 9 | 21.95 / 12.02 | 21.92 | 17.2 | 7.91 | held, 20.98 s |
| ang12 | defaults | ATC_ANG_RLL_P, ATC_ANG_PIT_P 12 | 21.80 / 11.98 | 21.77 | 17.1 | 7.95 | held, 20.96 s |
| tc0.05 | defaults | ATC_INPUT_TC 0.05 | 12.35 / 7.18 | 12.24 | 17.0 | 3.13 | held, 18.73 s |
| tc0.02 | defaults | ATC_INPUT_TC 0.02 | 11.36 / 6.19 | 10.02 | 16.9 | 2.75 | held, 18.68 s |
| acc1800 | defaults | ATC_ACC_R_MAX, ATC_ACC_P_MAX 1800 | 21.15 / 11.91 | 21.12 | 17.3 | 6.96 | held, 21.17 s |
| tc0.05acc1800 | defaults | ATC_INPUT_TC 0.05, ATC_ACC_R/P_MAX 1800 (= B1) | 11.76 / 6.15 | 10.95 | 16.5 | 2.80 | held, 18.70 s; base B1 |
| tc0.03acc1800 | defaults | ATC_INPUT_TC 0.03, ATC_ACC_R/P_MAX 1800 | 11.21 / 5.25 | 8.68 | 16.4 | 2.86 | held, 18.68 s |
| tc0.02acc1800 | defaults | ATC_INPUT_TC 0.02, ATC_ACC_R/P_MAX 1800 | 11.11 / 5.01 | 8.11 | 16.3 | 2.85 | held, 18.68 s |
| tc0.05acc1800ang9 | B1 | ATC_ANG_RLL/PIT_P 9 | 11.70 / 6.00 | 10.72 | 16.5 | 2.61 | held, 18.70 s |
| tc0.05acc1800ang12 | B1 | ATC_ANG_RLL/PIT_P 12 | 11.69 / 5.97 | 10.64 | 16.4 | 2.53 | held, 18.70 s |
| tc0.03acc1800ang9 | B1 | ATC_INPUT_TC 0.03, ATC_ANG_RLL/PIT_P 9 | 11.18 / 5.13 | 8.47 | 16.7 | 2.61 | held, 18.68 s |
| tc0.03acc1800ang12 | B1 | ATC_INPUT_TC 0.03, ATC_ANG_RLL/PIT_P 12 | 11.17 / 5.11 | 8.41 | 16.7 | 2.53 | held, 18.68 s |
| b05velp3 | B1 | PSC_NE_VEL_P 3 | 11.39 / 4.92 | 8.68 | 17.5 | 4.12 | held, 18.68 s |
| b05velp4 | B1 | PSC_NE_VEL_P 4 | 11.12 / 4.17 | 7.60 | 18.6 | 5.32 | held, 19.86 s |
| b05velp6 | B1 | PSC_NE_VEL_P 6 | 10.82 / 3.53 | 7.30 | 20.9 | 5.93 | held, 19.80 s |
| b05velp8 | B1 | PSC_NE_VEL_P 8 | 10.75 / 3.31 | 6.35 | 22.5 | 3.13 | held, 18.71 s |
| b05veli0.5 | B1 | PSC_NE_VEL_I 0.5 | 11.80 / 5.89 | 10.44 | 16.4 | 2.64 | held, 18.68 s |
| b05veli2 | B1 | PSC_NE_VEL_I 2 | 11.69 / 6.33 | 11.04 | 16.7 | 9.61 | held, 21.05 s |
| b05veld0 | B1 | PSC_NE_VEL_D 0 | 12.29 / 7.02 | 12.20 | 16.0 | 6.61 | held, 20.86 s |
| b05veld0.5 | B1 | PSC_NE_VEL_D 0.5 | 11.47 / 5.65 | 9.71 | 17.5 | 2.35 | held, 18.67 s |
| b05velp6d0.1 | B1 | PSC_NE_VEL_P 6, D 0.1 | 10.84 / 3.62 | 8.61 | 20.7 | 8.56 | held, 20.63 s |
| b05velp6d0.5 | B1 | PSC_NE_VEL_P 6, D 0.5 | 10.82 / 3.51 | 6.46 | 21.2 | 2.86 | held, 18.69 s |
| b05velp6i0.5 | B1 | PSC_NE_VEL_P 6, I 0.5 | 10.83 / 3.50 | 6.86 | 20.6 | 5.44 | held, 19.76 s |
| b05velp6i2 | B1 | PSC_NE_VEL_P 6, I 2 | 10.80 / 3.59 | 8.33 | 21.7 | 7.09 | held, 19.89 s |
| b05velp6pos1.5 | B1 | PSC_NE_VEL_P 6, PSC_NE_POS_P 1.5 | 11.00 / 3.50 | 7.50 | 21.1 | 5.09 | held, 19.77 s |
| b05velp6pos2 | B1 | PSC_NE_VEL_P 6, PSC_NE_POS_P 2 | 11.19 / 3.52 | 7.61 | 21.5 | 4.64 | held, 19.78 s |
| b05velp4pos1.5 | B1 | PSC_NE_VEL_P 4, PSC_NE_POS_P 1.5 | 11.25 / 4.12 | 7.76 | 19.0 | 4.52 | held, 19.80 s |
| rad0.1 | defaults | WP_RADIUS_M 0.1 | 26.38 / 7.64 | 26.37 | 17.5 | 36.72 | no hold: loiter point 36.7 cm from the last waypoint (60 s limit) |
| rad0.3 | defaults | WP_RADIUS_M 0.3 | 22.04 / 12.29 | 22.01 | 17.5 | 7.89 | held, 21.08 s |
| rad0.5 | defaults | WP_RADIUS_M 0.5 | 22.04 / 12.29 | 22.01 | 17.5 | 7.89 | held, 21.08 s |
| rad1 | defaults | WP_RADIUS_M 1 | 22.04 / 12.29 | 22.01 | 17.5 | 7.89 | held, 21.08 s |
| b05velp6d0.5rad0.5 | B1 | PSC_NE_VEL_P 6, D 0.5, WP_RADIUS_M 0.5 | 10.82 / 3.51 | 6.46 | 21.2 | 2.86 | held, 18.69 s |
| B2 | B1 | PSC_NE_VEL_P 6, D 0.5, WP_RADIUS_M 0.1 (= B2) | 10.82 / 3.39 | 6.41 | 20.9 | 2.64 | held, 19.01 s; base B2 |
| B2velp8 | B2 | PSC_NE_VEL_P 8 | 10.77 / 3.10 | 6.07 | 22.6 | 2.07 | held, 19.03 s |
| B2velp8d0.75 | B2 | PSC_NE_VEL_P 8, D 0.75 | 21.21 / 8.18 | 21.21 | 31.9 | 6.44 | oscillates: sustained swing at the 30 deg lean limit in the final hold |
| B2veli0.5 | B2 | PSC_NE_VEL_I 0.5 | 10.82 / 3.37 | 6.38 | 20.9 | 2.40 | held, 19.01 s |
| B2veld1 | B2 | PSC_NE_VEL_D 1 | 10.84 / 3.33 | 6.16 | 22.1 | 2.80 | held, 19.02 s |
| B2pos1.5 | B2 | PSC_NE_POS_P 1.5 | 11.00 / 3.27 | 5.54 | 21.3 | 2.52 | held, 19.04 s |
| B2ang9 | B2 | ATC_ANG_RLL/PIT_P 9 (= C) | 10.82 / 3.35 | 6.25 | 21.0 | 2.24 | held, 19.01 s; base C |
| B2ang12 | B2 | ATC_ANG_RLL/PIT_P 12 | 10.83 / 3.34 | 6.17 | 20.9 | 2.28 | held, 19.01 s |
| B2tc0.03 | B2 | ATC_INPUT_TC 0.03 | 10.80 / 3.04 | 5.55 | 20.5 | 2.69 | held, 19.02 s |
| B2ratp0.09 | B2 | ATC_RAT_RLL/PIT_P 0.09 | 10.81 / 3.41 | 6.55 | 21.2 | 2.97 | held, 19.01 s |
| B2ratp0.2 | B2 | ATC_RAT_RLL/PIT_P 0.2 | 10.82 / 3.39 | 6.31 | 20.7 | 2.62 | held, 19.01 s |
| B2ratd0.002 | B2 | ATC_RAT_RLL/PIT_D 0.002 | 10.82 / 3.39 | 6.42 | 21.1 | 2.49 | held, 19.01 s |
| B2ratd0.005 | B2 | ATC_RAT_RLL/PIT_D 0.005 | 10.82 / 3.40 | 6.40 | 20.7 | 2.76 | held, 19.01 s |
| B2ratd0.01 | B2 | ATC_RAT_RLL/PIT_D 0.01 | 10.82 / 3.40 | 6.35 | 20.3 | 3.05 | held, 19.01 s |
| B2wpjerk5 | B2 | WP_JERK 5 | 9.98 / 3.08 | 6.04 | 23.0 | 3.61 | held, 18.95 s |
| B2nejerk20 | B2 | PSC_NE_JERK 20 | 10.82 / 3.39 | 6.41 | 20.9 | 2.64 | held, 19.01 s |
| B2cnr2 | B2 | WP_ACC_CNR 2 | 10.82 / 6.49 | 10.76 | 23.4 | 3.95 | held, 24.02 s |
| C1 | C | ATC_INPUT_TC 0.03 | 10.81 / 3.01 | 5.42 | 20.8 | 2.68 | held, 19.02 s |
| C2 | C | ATC_INPUT_TC 0.03, PSC_NE_VEL_P 8 | 10.79 / 2.83 | 5.13 | 22.5 | 2.93 | held, 19.03 s |
| C3 | C | PSC_NE_VEL_P 8 | 10.78 / 3.10 | 5.89 | 22.7 | 2.51 | held, 19.03 s |
| C7 | C | PSC_NE_VEL_P 5 | 10.89 / 3.56 | 6.57 | 20.1 | 2.41 | held, 19.00 s |
| C6 | C | PSC_NE_POS_P 1.5 | 11.01 / 3.22 | 5.38 | 21.4 | 2.17 | held, 19.04 s |
| C4 | C | WP_JERK 2 | 11.16 / 3.23 | 5.21 | 21.0 | 2.33 | held, 18.99 s |
| C5 | C | WP_JERK 3 (= D) | 10.74 / 3.10 | 4.83 | 21.0 | 2.31 | held, 18.98 s; base D |
| D_p6d0.3 | D | PSC_NE_VEL_D 0.3 | 10.76 / 3.15 | 6.76 | 21.1 | 4.56 | held, 20.00 s |
| D_p6d0.75 | D | PSC_NE_VEL_D 0.75 | 10.75 / 3.16 | 4.77 | 21.7 | 2.49 | held, 18.97 s |
| D_p6d1 | D | PSC_NE_VEL_D 1 | 10.76 / 3.13 | 4.70 | 22.5 | 2.78 | held, 19.00 s |
| D_p6d1.25 | D | PSC_NE_VEL_D 1.25 | 80.86 / 29.22 | 80.85 | 38.8 | 91.11 | oscillates: sustained swing at the 30 deg lean limit in the final hold |
| D_p7 | D | PSC_NE_VEL_P 7 | 10.65 / 2.94 | 4.61 | 21.8 | 1.94 | held, 18.98 s |
| D_p8d0.5 | D | PSC_NE_VEL_P 8 | 10.59 / 2.85 | 4.49 | 22.8 | 2.17 | held, 18.99 s |
| D_p8d0.6 | D | PSC_NE_VEL_P 8, D 0.6 | 10.60 / 2.89 | 4.49 | 23.0 | 2.50 | held, 18.99 s |
| D_p9d0.5 | D | PSC_NE_VEL_P 9 | 22.05 / 4.39 | 22.04 | 32.2 | 3.39 | rejected: tilt over 25 deg (one swing to 32 deg on the approach to the last waypoint, then decays) |
| D_p10d0.5 | D | PSC_NE_VEL_P 10 | 35.18 / 7.51 | 35.18 | 32.7 | 5.32 | oscillates: sustained swing at the 30 deg lean limit in the final hold |
| D_i0.5 | D | PSC_NE_VEL_I 0.5 | 10.76 / 3.09 | 4.86 | 20.9 | 2.16 | held, 18.98 s |
| D_i2 | D | PSC_NE_VEL_I 2 | 10.72 / 3.13 | 4.87 | 21.1 | 3.11 | held, 18.98 s |
| D_pos1.25 | D | PSC_NE_POS_P 1.25 | 10.74 / 3.06 | 4.67 | 21.2 | 2.32 | held, 18.98 s |
| D_pos1.5 | D | PSC_NE_POS_P 1.5 | 10.74 / 3.03 | 4.53 | 21.4 | 2.26 | held, 18.99 s |
| D_pos2 | D | PSC_NE_POS_P 2 | 10.76 / 3.00 | 4.41 | 21.9 | 2.17 | held, 19.00 s |
| D_jerk2 | D | WP_JERK 2 | 11.16 / 3.23 | 5.21 | 21.0 | 2.33 | held, 18.99 s |
| D_jerk5 | D | WP_JERK 5 | 9.99 / 2.91 | 4.83 | 21.0 | 2.41 | held, 18.95 s |
| E1 | D | PSC_NE_POS_P 1.5, WP_JERK 5 (= tuned set) | 9.86 / 2.82 | 4.53 | 21.4 | 2.41 | **tuned set**; held, 18.96 s |
| abl_tc | tuned | ATC_INPUT_TC 0.1 (default) | 13.62 / 3.26 | 13.62 | 23.0 | 15.77 | ablation; no hold: loiter point 15.8 cm from the last waypoint (60 s limit) |
| abl_acc | tuned | ATC_ACC_R/P_MAX 1100 (default) | 9.92 / 3.17 | 5.58 | 22.7 | 2.56 | ablation; held, 18.98 s |
| abl_ang | tuned | ATC_ANG_RLL/PIT_P 4.5 (default) | 9.84 / 3.01 | 6.73 | 23.2 | 3.52 | ablation; held, 18.96 s |
| abl_pos | tuned | PSC_NE_POS_P 1 (default) | 9.99 / 2.91 | 4.83 | 21.0 | 2.41 | ablation; held, 18.95 s |
| abl_vel | tuned | PSC_NE_VEL_P 2, D 0.25 (defaults) | 11.51 / 5.45 | 9.37 | 16.8 | 2.51 | ablation; held, 19.02 s |
| E1_rad2 | tuned | WP_RADIUS_M 2 (default) | 9.86 / 2.99 | 4.54 | 21.8 | 2.58 | ablation; held, 18.65 s |
| abl_jerk | tuned | WP_JERK 1 (default) | 11.01 / 3.22 | 5.38 | 21.4 | 2.17 | ablation; held, 19.04 s |
| E1_p5 | tuned | PSC_NE_VEL_P 5 | 10.03 / 3.02 | 4.80 | 20.5 | 2.43 | margin probe; held, 18.96 s |
| E1_velp8 | tuned | PSC_NE_VEL_P 8 | 9.69 / 2.58 | 4.19 | 23.2 | 1.61 | margin probe; held, 18.98 s |
| E1_velp9 | tuned | PSC_NE_VEL_P 9 | 11.98 / 4.96 | 11.98 | 32.7 | 6.35 | margin probe; oscillates: sustained swing at the 30 deg lean limit in the final hold |
| E1_velp10 | tuned | PSC_NE_VEL_P 10 | 33.66 / 6.53 | 33.66 | 32.8 | 1.74 | margin probe; oscillates: sustained swing at the 30 deg lean limit in the final hold |
| E1_d0.25 | tuned | PSC_NE_VEL_D 0.25 | 9.85 / 3.00 | 8.68 | 21.7 | 5.34 | margin probe; held, 20.12 s |
| E1_d0.4 | tuned | PSC_NE_VEL_D 0.4 | 9.85 / 2.88 | 6.75 | 22.1 | 3.61 | margin probe; held, 19.89 s |
| E1_veld0.75 | tuned | PSC_NE_VEL_D 0.75 | 9.88 / 2.79 | 4.27 | 22.1 | 2.30 | margin probe; held, 18.96 s |
| E1_veld1 | tuned | PSC_NE_VEL_D 1 | 18.31 / 4.15 | 18.31 | 30.3 | 2.75 | margin probe; rejected: tilt over 25 deg (in the corners) |
| E1_veld1.25 | tuned | PSC_NE_VEL_D 1.25 | 66.71 / 21.43 | 66.67 | 40.0 | 61.48 | margin probe; oscillates: sustained swing at the 30 deg lean limit in the final hold |
| E1_d0.25p8 | tuned | PSC_NE_VEL_P 8, D 0.25 | 9.63 / 2.74 | 6.84 | 22.7 | 2.98 | margin probe; held, 18.98 s |
| E1_d0.25p9 | tuned | PSC_NE_VEL_P 9, D 0.25 | 9.60 / 2.56 | 4.36 | 23.6 | 0.90 | margin probe; held, 19.00 s |
| E1_d0.25p10 | tuned | PSC_NE_VEL_P 10, D 0.25 | 14.39 / 3.53 | 14.39 | 31.8 | 1.95 | margin probe; oscillates: sustained swing at the 30 deg lean limit in the final hold |
| E1_d0.4p8.5 | tuned | PSC_NE_VEL_P 8.5, D 0.4 | 9.65 / 2.57 | 4.27 | 23.5 | 1.25 | margin probe; held, 18.99 s |
| E1_pos2 | tuned | PSC_NE_POS_P 2 | 9.76 / 2.76 | 4.41 | 21.9 | 2.27 | margin probe; held, 18.98 s |
| E1_pos3 | tuned | PSC_NE_POS_P 3 | 9.66 / 2.83 | 7.05 | 23.2 | 2.34 | margin probe; held, 18.99 s |
| E1_pos4 | tuned | PSC_NE_POS_P 4 | 10.44 / 2.93 | 10.43 | 29.6 | 2.09 | margin probe; rejected: tilt over 25 deg (one swing at the last waypoint, then decays) |
| E1_ang12 | tuned | ATC_ANG_RLL/PIT_P 12 | 9.87 / 2.80 | 4.43 | 21.4 | 2.25 | margin probe; held, 18.96 s |
| E1_ratd0 | tuned | ATC_RAT_RLL/PIT_D 0 | 9.86 / 2.82 | 4.52 | 21.9 | 2.22 | margin probe; held, 18.96 s |
| E1_tc0.03 | tuned | ATC_INPUT_TC 0.03 | 9.80 / 2.50 | 3.54 | 21.2 | 2.51 | not adopted; held, 18.98 s |
| E1_wpacc1 | tuned | WP_ACC 1 (changes the course) | 9.51 / 2.25 | 3.64 | 13.4 | 1.62 | not adopted; held, 20.32 s |
