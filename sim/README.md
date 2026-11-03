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
