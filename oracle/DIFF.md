# ArduPilot code that the oracle copies or edits

The oracle proper (`build/oracle-nosincos`, and the `sincos` and `gcc` variants) compiles every
ArduPilot `.cpp` it uses from a checkout of ArduPilot at 802db19de1 (the `AP` variable of build.sh)
unmodified. No `.cpp` of the modules under test is copied or edited. The copies below are of code outside the
modules under test (the environment and the parameter loader), and one diagnostic copy that is not
part of the oracle.

## Verbatim copies in the stubs (no change to the body)

| copy | original | why |
|---|---|---|
| `stubs/AP_AHRS/AP_AHRS_View.h`, `oracle_calc_trig` | `AP_AHRS::calc_trig`, `libraries/AP_AHRS/AP_AHRS_Backend.cpp:93-135` | the trig values of the view; the real one is a member of the stubbed `AP_AHRS`. Only the name and `static` differ. The port has the same function (`Copter/AHRS.lean` `calc_trig`). |
| `stubs/oracle_env.cpp`, `AP_Param::set_value`, `setup_object_defaults`, `get_default_value` | `libraries/AP_Param/AP_Param.cpp:1501-1542`, `:2685-2696` | load the defaults of the real `var_info` tables; the rest of `AP_Param.cpp` needs storage and MAVLink. |
| `stubs/oracle_env.cpp`, `AP_HAL::Util::snprintf`, `set_soft_armed` | `libraries/AP_HAL/Util.cpp:46-53`, `:73-82` | `snprintf` unchanged; `set_soft_armed` without the watchdog `persistent_data` write. `Util.cpp` pulls in the printf engine. Neither affects a computed value. |
| `stubs/oracle_env.cpp`, `operator new`/`new[]` | `libraries/AP_Common/c++.cpp:40-75` | zero-filled allocation, which ArduPilot's classes rely on for members their constructors do not set. |

## Diagnostic copy (not the oracle): `diag/quaternion.cpp`

A copy of `libraries/AP_Math/quaternion.cpp`, used only by the `diag-floattrig` build variant to
test the root cause found in `RESULTS.md`. Every edit is marked `// ORACLE:` and sits under its own
switch (all on by default); with a switch at 0 the original lines are compiled.

| switch | function (original lines) | original | edited |
|---|---|---|---|
| `ORACLE_DIAG_EULER` | `QuaternionT<T>::from_euler(roll, pitch, yaw)` (`:423-428`) | `cosF(roll*0.5)`, ..., `sinF(yaw*0.5)` | `cosf(roll*0.5f)`, ..., `sinf(yaw*0.5f)` |
| `ORACLE_DIAG_AXIS` | `QuaternionT<T>::from_axis_angle(const Vector3<T> &axis, T theta)` (`:477`, `:479`) | `sinF(0.5*theta)`, `cosF(0.5*theta)` | `sinf(0.5f*theta)`, `cosf(0.5f*theta)` |
| `ORACLE_DIAG_ANGLE` | `QuaternionT<T>::angle(const QuaternionT<T> &v)` (`:839`, `:842`) | `vec_diff.length() * 0.5, 0.0, 1.0`; `2.0 * asinF(vec_len_div2)` | `* 0.5f, 0.0f, 1.0f`; `2.0f * asinf(vec_len_div2)` |

Plus a header comment and the three `#ifndef` switch defaults at the top of the file. The edits make
the copy compute what the Lean port computes (`AP_Math/quaternion.lean:77-98`: `Float32` sin/cos of
a `Float32` half angle). Result: with only `ORACLE_DIAG_AXIS` on, the oracle reproduces the port bit
for bit on all 8431 ticks; with only the other two on, it does not (RESULTS.md).

`diag/template_literal.cpp` is a ten-line test file (not linked anywhere) that shows the compiler
behavior behind the deviation.
