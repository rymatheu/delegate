# Oracle results: the 1 m/s figure-eight course

Flight: `sim/out/copter-course-1ms/copter-bin` (8431 ticks at 400 Hz, 21.08 s; parameters
`sim/params/copter-cf2x.txt` + `copter-course-speed.txt`). Open loop: every program below is fed
the recorded `inputs.txt`; the oracle's navigator targets are the recorded `trace.txt` columns 1-9
and AutoYaw switches to HOLD at tick 6618 (`probe/ModeSchedule.lean`). Reproduce with
`oracle/build.sh nosincos sincos gcc diag-floattrig && sim/.venv/bin/python oracle/compare.py`
(full tables in `build/compare/summary.txt`).

## Summary

1. **The oracle builds and runs the full 8431-tick stream deterministically**: every variant, two
   runs each, byte-identical output; no `INTERNAL_ERROR`, no parameter save, and the position
   error clamp never fires on the fed targets (so the fed targets are exactly what the port's
   navigator sent).
2. **Agreement**: the position controller agrees bit for bit on every tick. The desired
   position/velocity/acceleration it holds after the tick and the thrust vector it hands to the
   attitude controller (12 of the 22 numbers) are identical on all 8431 ticks. The parameters agree
   too: all 107 that both sides print are exactly equal.
3. **Divergence**: the attitude-controller outputs and the actuators differ from tick 496 (roll
   body-rate target `p_t`, 1 ulp) and tick 503 (actuator `m2`). On 1285 of 8431 ticks all 22
   numbers are equal, and on 1349 all four actuators are bit-identical. The largest difference
   over the flight is 1.09e-4 in an actuator and 1.5e-3 rad/s in a rate target.
4. **Root cause, one port deviation**: `QuaternionT<float>::from_axis_angle(axis, theta)` computes
   `sin`/`cos` of the half angle in double precision in ArduPilot and in single precision in the
   port. With that one function changed to the port's single-precision `sinf`/`cosf` (diagnostic
   variant), **the oracle reproduces the port bit for bit: all 22 numbers on all 8431 ticks.**
   The rest of the ported cascade has no other deviation that this flight exercises:
   `AC_PosControl`, `AC_AttitudeControl(_Multi)`, `AC_PID*`, `AP_Motors*`, the AP_Math subset,
   and the harness (takeover, Auto entry, first-tick loop time, fast-task order, AutoYaw).
5. The recording itself is not reproduced by the current port binary: it was made by a build that
   fused `sinf`/`cosf` into Apple's `__sincosf_stret` (`sim/README.md`, "Determinism"). The
   current binary `sim/build/copter-c` (`-fno-builtin-sinf -fno-builtin-cosf`) also differs from it
   from tick 496 (`m2` at 503). Comparisons below are therefore against both the recording and a
   fresh replay of the current binary. The replay is the port's semantics, since `Float32.sin` is
   `sinf`.

## Comparison numbers

Counts are ticks out of 8431. "first" is the first differing tick (1-based). Values are compared
exactly (the port prints exact decimals; it drops the sign of zero, so +0 = -0 here). An ulp
distance across zero is large by construction (`p_t` changes sign during the flight).

### Oracle (`oracle-nosincos`) vs the port (replay of `sim/build/copter-c`)

All 22 equal on 1285 ticks, first difference at tick 496. All four actuators bit-identical on 1349
ticks, first difference at tick 503.

| quantity | equal | differ | first | max abs diff | max ulp |
|---|---:|---:|---:|---:|---:|
| m1 | 1464 | 6967 | 532 | 1.09e-4 | 3646 |
| m2 | 1455 | 6976 | 503 | 1.09e-4 | 3644 |
| m3 | 1556 | 6875 | 532 | 6.44e-5 | 2161 |
| m4 | 1663 | 6768 | 532 | 6.44e-5 | 2160 |
| position target N, E, D | 8431 | 0 | - | 0 | 0 |
| velocity target N, E, D | 8431 | 0 | - | 0 | 0 |
| acceleration target N, E, D | 8431 | 0 | - | 0 | 0 |
| thrust vector N, E, D | 8431 | 0 | - | 0 | 0 |
| roll target | 2162 | 6269 | 1372 | 7.15e-7 | 49154 |
| pitch target | 1969 | 6462 | 1386 | 2.66e-7 | 40960 |
| yaw target | 4453 | 3978 | 1404 | 1.43e-6 | 23 |
| p target | 1729 | 6702 | 496 | 1.51e-3 | 2713650 |
| q target | 2391 | 6040 | 1348 | 4.94e-4 | 893440 |
| r target | 2833 | 5598 | 609 | 7.09e-6 | 591680 |

### Oracle vs the recording (`motors.txt`, `trace.txt`)

All 22 equal on 1726 ticks, first difference at tick 1206 (`r_t`). Actuators bit-identical on 1737
ticks, first difference at tick 1232 (`m3`). Position, velocity and acceleration targets and the
thrust vector are equal on all 8431 ticks. The max abs differences are 1.24e-4 (actuators), 1.52e-3
(`p_t`) and 1.42e-3 (`q_t`). The recording agrees with ArduPilot longer than the current port does
because `__sincosf_stret` returned the correctly rounded cosine at tick 496, where `cosf` does not
(see below).

### Port replay vs the recording

All 22 equal on 1277 ticks, first difference at tick 496 (`p_t`). Actuators bit-identical on 1355
ticks, first difference at tick 503 (`m2`). The position-controller columns are equal on all ticks.
This is the known fused/unfused difference of the port's own builds.

### Other oracle builds

- `oracle-sincos` (clang defaults) and `oracle-gcc` (g++ 15, `-fsingle-precision-constant`, which
  computes the same pair through `cexpf`): byte-identical output to `oracle-nosincos`, so the same
  numbers as above.
- `oracle-diag-floattrig` (the diagnostic copy of `quaternion.cpp`, `DIFF.md`) vs the port replay:
  **8431 of 8431 ticks with all 22 quantities equal; 8431 of 8431 with the four actuators
  bit-identical.** With only the `from_axis_angle` edit on (`-DORACLE_DIAG_EULER=0
  -DORACLE_DIAG_ANGLE=0`) the result is the same. With only the `from_euler` and `angle` edits on,
  the output is byte-identical to the unmodified oracle (those functions are not on this path).
- `--vehicle-calls` (`landed_gain_reduction(false)`, `set_reset_handling_method`,
  `set_desired_spool_state(THROTTLE_UNLIMITED)`, which the Lean harness leaves out): output
  byte-identical to the run without them, in both the oracle and the diagnostic variant.
- `--hold-from` 6617 or 6619 instead of 6618: the diagnostic variant then differs from the port
  from that tick on (`yaw_t`), so the switch tick is pinned down. Never switching gives yaw-target
  differences up to 0.46 rad after tick 6619.

## First divergence: tick 496

The first differing number is the roll body-rate target after tick 496: oracle
`0.112665958702564239501953125`, port `0.112665951251983642578125`, one float ulp apart. Everything
before it in the tick is equal, including the thrust vector the position controller hands over.
Instrumenting the original `from_axis_angle(axis, theta)` (a scratch copy that prints every call
whose double-precision and single-precision results differ, with the caller) gives the first such
call:

- tick 496, caller `AC_AttitudeControl::thrust_vector_rotation_angles`
  (`AC_AttitudeControl.cpp:1089`, `thrust_vector_correction.from_axis_angle(thrust_vec_cross,
  thrust_error_angle_rad)`), `theta = 0.00109183008`, half angle `h = 0.000545915042`.
  `(float)cos((double)h) = 0.999999821186065673828125` (1 - 3·2^-24), while
  `cosf(h) = 0.99999988079071044921875` (1 - 2^-24). The true cosine is
  0.99999985098838738663, which lies 0.49999999 ulp from the double-precision result and
  0.50000001 ulp from `cosf`'s: the true value is a near tie between the two floats, and Apple's
  `cosf` rounds it the wrong way. The sine agrees.
- The thrust-vector correction quaternion therefore differs in `q1` by one ulp. That changes the
  attitude error, hence `_ang_vel_body_rads.x`, the `p_t` of the trace. The rate controller uses it
  on the next ticks. The PID filters and integrators carry the difference, and it reaches an
  actuator's last bit at tick 503.
- Over the run (on the oracle's own trajectory) the double and single-precision results differ on
  204 calls of `from_axis_angle(axis, theta)` from three call sites:
  `thrust_vector_rotation_angles` (`:1089`, 88 calls) and `attitude_from_thrust_vector`
  (`:972`, 62, the thrust-vector quaternion; `:974`, 54, the heading quaternion at headings near
  45 degrees). In every one of the 204 the double-precision result is the correctly rounded one
  (99 sines, 105 cosines checked against a 120-bit evaluation), and the single-precision libm
  result is 1 ulp off.

## Port deviations found

### 1. `Quaternion.from_axis_angle_theta`: single-precision trig where ArduPilot uses double (exercised; the cause of every difference above)

- C++: `libraries/AP_Math/quaternion.cpp:468-483`, `QuaternionT<T>::from_axis_angle(const
  Vector3<T> &axis, T theta)`, lines 477 and 479: `const T st2 = sinF(0.5*theta);` and
  `q1 = cosF(0.5*theta);`. With `HAL_WITH_EKF_DOUBLE` (SITL) `ftype.h:14-21` defines
  `sinF(x)` as `sin(x)` and `cosF(x)` as `cos(x)`. The function is a template, and Apple clang does
  not apply `-cl-single-precision-constant` inside a template, so `0.5` is a `double`, `0.5*theta`
  is a double product (exact), and the call is the double `sin`/`cos`, rounded once to `float` on
  assignment. The compiled code: `fcvt d0, s0; fmul d8, d1, d0; bl _sin; fcvt s9, d0; ...; bl _cos;
  fcvt s0, d0` (`objdump` of `build/oracle-nosincos`). `diag/template_literal.cpp` shows the
  compiler rule in isolation: the same expression in an ordinary function compiles to `fmul s; b
  _sinf`, and in a function template to `fcvt d; fmul d; bl _sin; fcvt s`. The rotation-vector form
  `from_axis_angle(Vector3<T> v)` (`:453-465`) calls this one, so both forms are affected. With
  GCC the literal is `float`, but `sin(float)` resolves to `std::sin(float)` and GCC merges the
  pair into one `cexpf` call on this host; on this flight that gives the same results as clang's
  double path, and neither is the port's separate `sinf`/`cosf`.
- Lean: `AP_Math/quaternion.lean:93-98`, `from_axis_angle_theta`: `let st2 := (0.5 * theta).sin`,
  `⟨(0.5 * theta).cos, ...⟩` (`Float32.sin`/`cos`, `sinf`/`cosf`). It is called from
  `AC_AttitudeControl.lean:579-580` (`attitude_from_thrust_vector`), `:613`
  (`thrust_vector_rotation_angles`), and through `Quaternion.from_axis_angle` (`:101-104`) from
  `:466`, `:586`, `:644`, `:727`.
- The port's own header states the opposite: `AP_Math/quaternion.lean:15-25` says the `sinF`/`cosF`
  macros resolve to `sinf`/`cosf`. The check it cites compiled a non-template function. That
  holds for ordinary functions but not for the `QuaternionT<T>` template under clang.
- Evidence: the `diag-floattrig` run (bit-identical on all 8431 ticks once this one function uses
  `sinf`/`cosf`), the 204 mismatching calls above, the disassembly.
- Size: one ulp in a quaternion component, on 204 calls in 8431 ticks. In open loop this grows to at
  most 1.09e-4 in an actuator (hover throttle is 0.4444) and 1.5e-3 rad/s in a rate target.
- A fix for whoever is assigned (not applied): in `from_axis_angle_theta`, compute the half-angle
  sine and cosine as the C++ does. The value is `Float.sin (0.5 * theta.toFloat)`, rounded to
  `Float32` (the product is exact in either precision; `Float.sin` is `sin`). The same applies to
  `from_euler`, below.

### 2. `Quaternion.from_euler`: the same pattern (latent; not exercised by this flight)

- C++: `quaternion.cpp:423-428`, `cosF(roll*0.5)` ... `sinF(yaw*0.5)`. These are double `cos`/`sin`
  of a double half angle, for the same reasons as above (`objdump`: three `bl _cos`, three `bl _sin`
  in `QuaternionT<float>::from_euler`).
- Lean: `AP_Math/quaternion.lean:77-84` (`(roll * 0.5).cos` etc., `Float32`).
- Not on the Auto path (the C++ callers are `AC_AttitudeControl.cpp:447`, `:526`, `:584`, the
  `input_euler_*` methods). The diagnostic edit of `from_euler` changes nothing on this flight. It
  is a deviation on any path that reaches it.

### No other deviation on this flight

Once deviation 1 is neutralized, the 22 traced numbers agree on every tick. So do the actuators,
which depend on the whole cascade (rate PIDs, mixer, thrust curve, throttle filter, angle boost).
The other places where the compiled C++ widens a `float` to `double` were also checked in the
disassembly. They are the `postype_t` position arithmetic, which the port models as `Float`, and
the comparisons of the inline template `is_negative` against `-1.0 * FLT_EPSILON`, which are
exact in either precision. Neither can change a value.

## Environment conventions the oracle copies from the port (not deviations of ported code)

- `get_quat_body_to_ned` returns the sample quaternion itself. ArduPilot's view returns
  `from_rotation_matrix(rot_body_to_ned)` of the EKF's matrix (`AP_AHRS_View.h:55-57`). The rotation
  matrix, Euler angles and trig values are derived from the sample as `Copter/AHRS.lean` does.
- `get_gyro_latest` is the sample gyro without the identity `rot_view` product (`AP_AHRS_View.cpp:86-88`).
- The motors start armed, interlocked and in `THROTTLE_UNLIMITED`. A real flight reaches that state
  through the spool-up logic.
- The navigator and the mission (WPNav/SimplePath, the submode schedule) are the port's: fed from
  its trace and the probe.

## Status after commit f50cd92

The deviation in `from_axis_angle` (and `from_euler`) is fixed in `AP_Math/quaternion.lean`: the half-angle sine and cosine are now evaluated in double precision and narrowed, as the compiled C++ does. With that change the unmodified-ArduPilot variant `oracle-nosincos` matches a fresh replay of `sim/build/copter-c` on all 22 numbers on all 8431 ticks, actuators bit-identical on every tick. The `diag-floattrig` variant now models the superseded single-precision behavior and differs from the port from tick 496. The paragraphs above describe the state before the fix.
