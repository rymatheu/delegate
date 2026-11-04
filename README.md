# ArduCopter in Lean 4, verified as the source that runs

A class-by-class port of ArduCopter (ArduPilot commit 802db19de1, master after 4.7, SITL build configuration) to Lean 4, verified as the very source code that runs, compared bit for bit with ArduPilot's own C++ classes, and flown in simulation from the same source compiled to C.

The port keeps ArduPilot's structure: one Lean directory per ArduPilot library, one namespace per C++ class, the same method and parameter names (conventions in `PORT.md`). Control quantities are `Float32` (ArduPilot's `float`) and positions `Float` (ArduPilot's `postype_t`, which is `double` in SITL); the quaternion half-angle trigonometry is computed in `double` and narrowed, as the C++ compiles under Apple clang. The main loop runs at 400 Hz in ArduCopter's fast-task order: rate controller, motors output, AHRS and inertial estimates, `update_flight_mode`. The port is the object of every theorem. It is lifted, as source, to a set of behaviors; specifications are discrete-time signal temporal logic formulas read as sets of behaviors; a contract `(A, G)` holds of a component `M` when `M ∩ A ⊆ G`. Floating-point rounding enters the proofs through Lean's own bit-level models of binary32 and binary64 (`Float32.Model`, `Float.Model`), from which the needed rounding bounds are proved. No `sorry` and no `axiom` declaration: every theorem depends only on `propext`, `Classical.choice` and `Quot.sound`. Facts about functions that Lean declares as opaque (the C library, width conversions, sensing) are explicit hypotheses.

## Layout

| Directory | Contents |
|---|---|
| `AP_Math/` | `AP_Math`, `control`, `definitions`, `location`, `vector2`, `vector3`, `matrix3`, `quaternion`, and the numeric types `ftype` and `postype` (`ftype.lean`). |
| `AC_PID/` | `AC_PID`, `AC_PID_2D`, `AC_PID_Basic`, `AC_P`, `AC_P_1D`, `AC_P_2D`, `AP_PIDInfo`. |
| `AC_AttitudeControl/` | `AC_AttitudeControl`, `AC_AttitudeControl_Multi`, `AC_PosControl`. |
| `AC_WPNav/` | `AC_WPNav`, with `SimplePath` in place of ArduPilot's SCurve path generator. |
| `AP_Motors/` | The motors interface, `AP_Motors_Thrust_Linearization`, `AP_MotorsMulticopter`, `AP_MotorsMatrix` (quad X). |
| `Copter/` | The vehicle: `Parameters`, `AHRS`, `State`, `AutoYaw`, `ModeAuto`, `Loop` (one tick in fast-task order), and the executables `Main` (`copter`, the lock-step controller, protocol in `Copter/PROTOCOL.md`) and `Bench` (`bench`, per-tick timing). |
| `FloatModel/` | The exact real value of a float and rounding bounds for `+`, `-`, `*`, `/`, `sqrt`, generic over the format and instantiated at binary32 and binary64, proved from `Float32.Model` and `Float.Model`. |
| `Contracts/` | Contract algebra, STL, lifts of code to behavior sets, the plant model, and the theorems about the port (`Copter*`). |
| `oracle/` | ArduPilot's own classes compiled unmodified with stub headers, driven open loop on recorded samples and compared with the port; the timing benchmark. |
| `sim/` | The closed-loop simulation in gym-pybullet-drones, the C build, and the parameter files. |

`Flight/`, `Contracts/Quad*.lean` and `Contracts/FloatLoop*.lean` are the previous stack (see "Previous stack" below).

## What is proved

| Theorem | File | Statement |
|---|---|---|
| `Contracts.CopterCode.actuators_in_unit` | `Contracts/CopterCode.lean` | For every parameter record, every actuator output of the port is a finite float in `[0, 1]` at every tick, for every input stream, with no hypotheses. |
| `Contracts.CopterHover.hover_invariant` | `Contracts/CopterHover.lean` | The port with the hover mission and the run parameters, closed with the rigid-body plant of `Contracts/CopterPlant.lean` and started level and exactly at rest at the hover setpoint, stays within 5 mm of the setpoint altitude and 1 cm/s of rest, level and horizontally fixed, for every horizon `T`. The guarantee is the STL formula `initOn (·.phys) (.always 0 T hoverBox)`. `hover_invariant_nonvacuous` shows the contract is not vacuous. |
| `Contracts.CopterVert.contr` | `Contracts/CopterVert.lean` | The six-state vertical recurrence of the hover has a quadratic Lyapunov function that contracts by `249/250` per tick. |
| `Contracts.CopterVertNear.vert_tick` | `Contracts/CopterVertNear*.lean` | One tick of the `Float32` vertical code follows the recurrence within a rounding budget: thirty binary32 operations, 277 times under the slack. |
| Zero propagation | `Contracts/CopterZero*.lean` | At a level sample, every horizontal and rotational quantity of the port is exactly zero. |
| `add_error`, `sub_error`, `mul_error`, `*_small`, `div_err_all`, `sqrt_err_all` | `FloatModel/` | Rounding bounds for both formats: relative error of one unit roundoff in the normal range, exact sums and differences and an absolute bound for products below it, division and square root; with bracket lemmas. |
| `Contracts.Float32ClipAP.constrain_float_spec`, `constrain_float_toReal` | `Contracts/Float32Clip.lean`, `Contracts/Float32ClipAP.lean` | ArduPilot's `constrain_float` on finite bounds `lo ≤ hi` with `\|lo + hi\| ≤ maxFinite32`: for every input, NaN and infinities included, the result is finite and in `[lo, hi]` (on NaN it returns `(lo + hi) / 2`, as the C++ does); on a finite input it is the real clamp. |
| `Contracts.chain`, `compose_refines`, `refines_sound` | `Contracts/Basic.lean` | The contract algebra: saturation, refinement, composition, and the chain rule. |

The hypotheses of `hover_invariant` are structures of `Prop` about functions that Lean declares as opaque externs, so they cannot be proved inside Lean:

- `LibmZero32` (`Contracts/CopterZero.lean`): `acosf 1 = 0`, `sinf ±0 = ±0`, `cosf 0 = 1`, and `atan2f(±0, x) = ±0` for `x > 0`.
- `LibmCos32` (`Contracts/CopterHoverMotorInit.lean`): `cosf` of a finite argument is finite.
- `ConvZero` (`Contracts/CopterZero.lean`): the width conversions send zero to zero.
- `NarrowSpec 2` (`Contracts/CopterVertNear.lean`): `Float.toFloat32` rounds within the binary32 unit roundoff.
- `WidenSpec` (`Contracts/CopterHoverUniverse.lean`): `Float32.toFloat` is exact.
- `CopterSense` (`Contracts/CopterPlant.lean`): the sensing maps return finite values within rounding of the real state.

To list the axioms yourself:

```
cat > axioms.lean <<'EOF'
import Contracts
#print axioms Contracts.CopterHover.hover_invariant
#print axioms Contracts.CopterCode.actuators_in_unit
EOF
lake env lean axioms.lean
```

## Trusted base

- The Lean 4 kernel and the toolchain pinned in `lean-toolchain` (`v4.33.0-rc1`), with Mathlib at the matching tag.
- Lean's `Float.Model` and `Float32.Model` as faithful models of IEEE 754 binary64 and binary32, and the assumption that the compiled code's arithmetic agrees with them: the Lean compiler's C emitter and clang as invoked by `leanc`, which passes `-ffp-contract=off` (no fused multiply-adds). The lakefile adds `-fno-builtin-sinf -fno-builtin-cosf -fno-builtin-sin -fno-builtin-cos`, because clang otherwise fuses a sine and a cosine of the same argument into one call of `__sincosf_stret` or `__sincos_stret`, which is not bit-identical to the separate libm calls.
- The C library at the points named by the hypotheses above.
- The plant model (`Contracts/CopterPlant.lean`): rigid-body dynamics with the CF2X constants of gym-pybullet-drones. The simulation is a check of this model, not a proof about it.
- The statement of each theorem.

## Oracle

`oracle/` compiles ArduPilot's own classes (`AC_PosControl`, `AC_AttitudeControl` and `AC_AttitudeControl_Multi`, `AP_Motors*`, the `AC_PID` family, `AP_Math`) unmodified, with stub headers for their environment (Route 2 in `oracle/NOTES.md`), and drives them open loop on the samples recorded from a flight of the port. Since the port's `from_axis_angle` computes its half-angle sine and cosine in double precision, as the C++ does, the port and the C++ agree on all 22 numbers (four actuators and 18 trace values) of all 8431 ticks (`oracle/RESULTS.md`, `oracle/DIFF.md`). The benchmark (`oracle/BENCH.md`, `Copter/Bench.lean`, `oracle/bench.py`) measures a pure tick on the recorded course: 3.49 ± 0.19 µs for the port, 0.76 ± 0.05 µs for the C++.

ArduPilot's source is not part of this repository. The oracle needs a checkout of https://github.com/ArduPilot/ardupilot at commit 802db19de1, whose path is given by the `AP` environment variable (default: `ardupilot` next to this repository; submodules are not needed). From the repository root:

```
git clone https://github.com/ArduPilot/ardupilot ../ardupilot
git -C ../ardupilot checkout 802db19de1
AP=../ardupilot oracle/build.sh               # oracle/build/oracle-nosincos (the oracle) and oracle-sincos
sim/.venv/bin/python oracle/compare.py        # replay the port, run every built variant, compare
python3 oracle/bench.py                       # the timing benchmark
```

`oracle/README.md` documents the build variants, the stubs and the harness.

## Building

Requires `elan`. Mathlib is a dependency, so fetch its prebuilt cache before building:

```
lake exe cache get
lake build
```

`lake build` builds the libraries and the executables `copter` and `flight`; `lake build bench` builds the benchmark. `lake exe copter --selftest` runs 100 ticks of hover at a fixed sample.

`copter` runs in lock step over standard input and output, one 400 Hz tick per text line: 17 numbers in (`x y z vx vy vz ax ay az q1 q2 q3 q4 p q r dt`: NED position, velocity and specific force, the body-to-NED quaternion, body rates, period), four actuator values out, as exact decimals with `--exact`. Parameters are set by ArduPilot name with `--params FILE` and `--set "NAME VALUE"`. `Copter/PROTOCOL.md` has the format and the options.

## Running the experiment

The port flies a figure-eight course on a CF2X in gym-pybullet-drones 2.2.0 (physics 1200 Hz, control 400 Hz, gravity 9.80665, PyBullet's velocity damping off) through three routes that produce the same actuator commands bit for bit: `lake exe copter`, a standalone binary compiled from the C that Lean emits, and Lean's interpreter. Set up the simulator as described in `sim/README.md`, then:

```
sim/build_copter_c.sh                                  # the C route: sim/build/copter-c
cd sim
.venv/bin/python run_copter.py --determinism --params params/copter-cf2x.txt \
  --params params/copter-course-speed.txt --duration 60 --out out/copter-course-1ms     # ArduPilot default gains
.venv/bin/python run_copter.py --determinism --params params/copter-cf2x.txt \
  --params params/copter-course-speed.txt --params params/copter-cf2x-tuned.txt \
  --duration 60 --out out/copter-tune-final-det                                         # tuned gains
.venv/bin/python run_copter.py --determinism --params params/copter-cf2x.txt --params params/copter-hover.txt \
  --duration 10 --hold 99 --out out/copter-hover                                        # hover at 1 m
```

`--backend bin`, `lake` or `interp` flies one route instead of all three; `--gui` opens a window. Results and logs go to the `--out` directory. The parameter files use ArduPilot names:

- `sim/params/copter-cf2x.txt`: the vehicle, with linear thrust (`MOT_THST_EXPO 0`, `MOT_SPIN_MIN 0`, `MOT_SPIN_MAX 1`, `MOT_HOVER_LEARN 0`, `MOT_THST_HOVER 0.4444`), and the figure-eight mission; every gain at its ArduPilot default.
- `sim/params/copter-course-speed.txt`: path speed 1 m/s (`WP_SPD 1`, `WP_ACC 1.5`).
- `sim/params/copter-hover.txt`: a single waypoint 1 m above the origin.
- `sim/params/copter-cf2x-tuned.txt`: the tuned overlay (`ATC_INPUT_TC 0.05`, `ATC_ACC_R_MAX`/`ATC_ACC_P_MAX 1800`, `ATC_ANG_RLL_P`/`ATC_ANG_PIT_P 9`, `PSC_NE_POS_P 1.5`, `PSC_NE_VEL_P 6`, `PSC_NE_VEL_D 0.5`, `WP_RADIUS_M 0.1`, `WP_JERK 5`); `sim/README.md`, "Tuning", records how it was found.

Recorded results on the 1 m/s course:

| Gains | Duration | Tracking error, max / rms | Final error | Motor lines differing among the three routes |
|---|---|---|---|---|
| ArduPilot defaults | 21.08 s, 8431 ticks | 22.0 / 12.3 cm | 7.89 cm | 0 |
| Tuned | 18.97 s, 7586 ticks | 9.9 / 2.8 cm | 2.41 cm | 0 |

### Previous stack

The first version of this work, superseded by the ArduCopter port, is kept in the repository and still builds: `Flight/` (a quadcopter controller written directly in Lean over `Float`, executable `flight`), its theorems in `Contracts/Quad*.lean` and `Contracts/FloatLoop*.lean` (`QuadCode.motors_in_unit`, `QuadHover.hover_invariant_nearest`, `FloatLoopIEEE.loop_spec_nearest`), and its simulation driver `sim/run_demo.py`, C build `sim/build_c.sh` and parameter files `sim/params/cf2x.txt`, `cf2x-course.txt`, `hover.txt`.

## Toolchain

Lean `v4.33.0-rc1` with Mathlib at the matching tag (see `lake-manifest.json`). The simulation used gym-pybullet-drones 2.2.0, PyBullet 3.2.7 and Python 3.12 on macOS; `sim/README.md` records the versions and the install steps. The oracle was built with Apple clang 17.
