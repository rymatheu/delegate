# C++ oracle for the Lean ArduCopter port

The oracle runs ArduPilot's own control classes, compiled unmodified from
`/Users/ryan/Research/delegate/ardupilot` (commit 802db19de1), on the samples recorded from a flight
of the Lean port, and prints, tick by tick, what the port prints (`Copter/PROTOCOL.md`): the four
actuator values and the 18 `--trace` numbers. `compare.py` compares the two. Results:
`RESULTS.md`. Copied or edited ArduPilot code: `DIFF.md`. This is Route 2 of `NOTES.md`.

## Build and run

```sh
oracle/build.sh                      # builds build/oracle-nosincos (the oracle) and build/oracle-sincos
oracle/build.sh gcc diag-floattrig   # optional: the GCC build and the diagnostic variant
sim/.venv/bin/python oracle/compare.py   # replay the port, run every built variant, compare
```

One run by hand (from the package root):

```sh
D=sim/out/copter-course-1ms/copter-bin
oracle/build/oracle-nosincos --nav $D/trace.txt --hold-from 6618 \
    --params sim/params/copter-cf2x.txt --params sim/params/copter-course-speed.txt \
    < $D/inputs.txt > oracle.txt
```

Options: `--nav FILE` (the navigator's outputs, see Harness; a file of 18-number `trace.txt` lines
or 22-number `copter --trace` lines), `--params FILE` and `--set "NAME VALUE"` (the port's override
format: ArduPilot names, `#` comments, `waypoint` lines ignored), `--hold-from N`, `--vehicle-calls`
(see Harness), `--print-params` (every parameter of the compiled tables plus the harness values,
exact). Output, one line per input line: `m1 m2 m3 m4`, then the 18 trace numbers (position,
velocity, acceleration targets after the tick, thrust vector, attitude-target Euler angles,
body-rate targets), all as exact decimals in the port's format, then `|` and the bit patterns of
the same 22 values (hex; float32, the position float64). A summary on standard error gives the
tick count, the number of ticks on which the position error clamp fired on the fed target, the
`INTERNAL_ERROR` reports and the parameter saves (all 0 on the recorded flight).

`--hold-from` is the tick (1-based) at which the mission completes and `ModeAuto::loiter_start`
switches AutoYaw to HOLD. The navigator is not compiled, so this comes from the port:

```sh
lake env lean --run oracle/probe/ModeSchedule.lean $D/inputs.txt \
    sim/params/copter-cf2x.txt sim/params/copter-course-speed.txt
```

prints the ticks at which the submode, the AutoYaw mode or the mission item change (tick 6618:
`LOITER HOLD` for the recorded flight; 6617 and 6619 do not reproduce the port, 6618 does).

Build variants (`build.sh VARIANT...`): `nosincos` (the oracle: Apple clang 17,
`-fno-builtin-sinf -fno-builtin-cosf`, the flags of the port binary `sim/build/copter-c`),
`sincos` (clang defaults; it links no `__sincosf_stret` either, and its output is byte-identical),
`gcc` (Homebrew g++ 15 with GCC's `-fsingle-precision-constant`, as a Linux SITL build; on this host
GCC turns each `sinf`/`cosf` pair into one `cexpf` call; output byte-identical to the clang
oracle on this flight), `diag-floattrig` (diagnostic only, see `DIFF.md`).

## What is compiled unmodified

From `libraries/`, every function body under test is ArduPilot's:

| file | why |
|---|---|
| `AC_AttitudeControl/AC_PosControl.cpp` | port: `AC_AttitudeControl/AC_PosControl.lean` |
| `AC_AttitudeControl/AC_AttitudeControl.cpp`, `AC_AttitudeControl_Multi.cpp` | port: `AC_AttitudeControl.lean`, `AC_AttitudeControl_Multi.lean` |
| `AP_Motors/AP_MotorsMulticopter.cpp`, `AP_MotorsMatrix.cpp`, `AP_Motors_Thrust_Linearization.cpp` | port: `AP_Motors/*.lean` |
| `AP_Motors/AP_Motors_Class.cpp` | base class of the above (constructor, `armed`, `rc_write`, ...) |
| `AC_PID/AC_PID.cpp`, `AC_PID_2D.cpp`, `AC_PID_Basic.cpp`, `AC_P.cpp`, `AC_P_1D.cpp`, `AC_P_2D.cpp` | port: `AC_PID/*.lean` |
| `AP_Math/AP_Math.cpp`, `control.cpp`, `vector2.cpp`, `vector3.cpp`, `matrix3.cpp`, `quaternion.cpp` | port: `AP_Math/*.lean` |
| `Filter/LowPassFilter.cpp` | the motors' throttle filter, the PID filters (ported inline) |
| `Filter/SlewLimiter.cpp` | dependency of `AC_PID` (inactive, see below) |
| `Filter/DerivativeFilter.cpp` | dependency of `AP_MotorsMulticopter` (inactive, see below) |
| `AP_Param/AP_ParamT.cpp` | `AP_Float::set_and_save` etc. (templates of the real `AP_Param.h`) |

Not compiled: `AC_WPNav` (its outputs come from the trace), the AHRS/EKF (the stub returns the
sample), the notch and harmonic-notch filters (compiled out by `AP_FILTER_ENABLED 0`), AutoTune,
custom controllers, the vehicle code. The headers of the real tree are used wherever they compile:
`AP_HAL` (with `AP_HAL/board/sitl.h` and `AP_HAL_SITL/Semaphores.h`), `AP_Param/AP_Param.h`,
`AP_Common`, `AP_Math`, `Filter`, `AC_PID`, `AC_AttitudeControl`, `AP_Motors`,
`SRV_Channel/SRV_Channel.h`, `AP_BoardConfig/AP_BoardConfig.h`, `AP_InternalError`,
`AP_CustomRotations`, `RC_Channel`, `AP_Logger/LogStructure.h` and `AP_Logger_config.h`.

Dependencies that the port lacks and that are inactive in the port's configuration (each one
leaves the values exactly unchanged; the bit-identical diagnostic run in `RESULTS.md` confirms it
on the whole flight):
- `AP_MotorsMulticopter::update_throttle_filter`'s throttle slew-rate detector (`DerivativeFilter`,
  `_throttle_slew_filter`, `AP_MotorsMulticopter.cpp:366-374`): its only consumer,
  `AC_AttitudeControl_Multi::update_throttle_gain_boost` (`AC_AttitudeControl_Multi.cpp:416-426`),
  multiplies the PD and angle-P scales by `constrain_float(ATC_THR_G_BOOST + 1, 1, 2) = 1` at
  `ATC_THR_G_BOOST = 0`, an exact identity.
- `AC_PID`'s `SlewLimiter` (`AC_PID.cpp:274-279`): `ATC_RAT_*_SMAX = 0`, so
  `SlewLimiter::modifier` returns 1 (`SlewLimiter.cpp:83-85`) and `P_out *= 1`.
- `AC_PID` `PDMX = 0` (`AC_PID.cpp:287`): the PD limit is skipped.
- Battery-voltage compensation: `MOT_BAT_VOLT_MAX = 0` takes the early exit of
  `update_lift_max_from_batt_voltage` (`AP_Motors_Thrust_Linearization.cpp:161-166`: `lift_max = 1`).
- Current limiting: `MOT_BAT_CURR_MAX = 0` (`AP_MotorsMulticopter.cpp:388-396`).
- Air-density compensation (`AP_MOTORS_DENSITY_COMP 1`,
  `AP_Motors_Thrust_Linearization.cpp:10-17`): the stub ratio is `run.air_density_ratio = 1`.

## Stubs (`stubs/`, ahead of `libraries/` on the include path)

Each file starts with a header saying what it replaces and why.

| stub | replaces | what it fakes |
|---|---|---|
| `ap_config.h` | waf's generated `build/sitl/ap_config.h` (`-include`) | the SITL `cfg.define()`s (`boards.py:886-893`) and `_GNU_SOURCE` |
| `hwdef.h` | waf's generated SITL `hwdef.h` (`AP_HAL/board/sitl.h:3`) | the defines of `AP_HAL_SITL/hwdef/sitl/hwdef.dat` |
| `AP_AHRS/AP_AHRS.h` | the EKF front end | getters return the scripted sample: `get_relative_position_NED_origin` (double), `get_relative_position_D_origin_float`, `get_velocity_NED`, `get_vert_pos_rate_D`, `get_accel_ef`; `get_control_gain_scaler_XY/Z` = 1; `get_air_density_ratio` = `run.air_density_ratio`; reset counts 0 |
| `AP_AHRS/AP_AHRS_View.h` | the AHRS view (header and `.cpp`) | `get_quat_body_to_ned` = the sample quaternion, `rot_body_to_ned` = its `rotation_matrix()`, `roll/pitch/yaw` = `to_euler()`, trig values by a verbatim copy of `AP_AHRS::calc_trig`, `get_gyro_latest` = the sample gyro; exactly the port's environment, `Copter/AHRS.lean` |
| `SITL/SITL.h` | the simulator singleton (reached via `AP_AHRS_SIM.h`) | `AP::sitl()->state.is_lock_step_scheduled = true` (`AC_PosControl::has_good_timing`, diagnostics) |
| `AP_Scheduler/AP_Scheduler.h` | the scheduler | `ticks32()`, `ticks()`, `get_loop_rate_hz()` = 400, `get_loop_period_s()`, `get_last_loop_time_s()`, `get_filtered_loop_time()`, advanced by the harness |
| `AP_Logger/AP_Logger.h` | the logger | `Write*`: dropped |
| `GCS_MAVLink/GCS_MAVLink.h`, `GCS.h` | MAVLink (the submodule is empty) | `MAV_TYPE`, `MAV_SEVERITY`, `GCS_SEND_TEXT` (dropped) |
| `AP_Vehicle/AP_Vehicle.h` | the vehicle base class (`AC_AttitudeControl.cpp:3`) | nothing is used; includes the real `AP_Vehicle_Type.h` |
| `AP_BattMonitor/AP_BattMonitor.h` | battery monitor | 0 V, no current sensor |
| `AP_Baro/AP_Baro.h` | barometer (`AP_Motors_Thrust_Linearization.cpp:5`) | empty, nothing is used |
| `AP_Notify/AP_Notify.h` | notifications | `AP_Notify::flags.armed` only |
| `oracle_env.cpp` | out-of-line definitions | the singletons (`AP::ahrs()`, `AP::scheduler()`, ...); the HAL clock (`AP_HAL::micros/millis` = the sum of the fed loop times, as `Copter/State.lean`); a HAL with a no-op `RCOutput` and a `Util`; `AP_InternalError::error` (counted, printed); `AP_CustomRotations` (panics: never used); `AP_Param::setup_object_defaults`, `set_value`, `get_default_value` (verbatim copies, no storage) and `save` (counted no-op); zero-filling `operator new` (as `AP_Common/c++.cpp:40-75`; ArduPilot objects rely on it); `SRV_Channels` statics (no-op output routing; a zero-filled `_singleton`, read by `rc_set_freq`); `AP_BoardConfig::config_error` (abort); `AP_HAL::Util::snprintf` and `set_soft_armed` |

## Defines and flags (`build.sh`)

`-DCONFIG_HAL_BOARD=HAL_BOARD_SITL -DCONFIG_HAL_BOARD_SUBTYPE=HAL_BOARD_SUBTYPE_NONE
-DAP_SCRIPTING_CHECKS=1 -DAP_BARO_PROBE_EXTERNAL_I2C_BUSES=1 -DHAL_NAVEKF2_AVAILABLE=1`
(`boards.py:877-893, :900`); `-DARDUPILOT_BUILD`; `-DAPM_BUILD_DIRECTORY=APM_BUILD_ArduCopter
-DAP_BUILD_TARGET_NAME="ArduCopter"` (`ardupilotwaf.py:143-144`; selects the Copter defaults of
`AC_PosControl`; any vehicle build gets `AP_MOTORS_DENSITY_COMP 1`); `-DFRAME_CONFIG=MULTICOPTER_FRAME`
(`ArduCopter/wscript:47`); `-D__AP_LINE__=__LINE__` (`boards.py:669`);
`-DHAL_WITH_POSTYPE_DOUBLE=1 -DHAL_WITH_EKF_DOUBLE=1` (SITL's defaults,
`AP_HAL_Boards.h:385-386`, `board/sitl.h:88-89`, made explicit); `-DAP_FILTER_ENABLED=0` (compiles
the `AC_PID` notch paths out; the port has no notch filtering). From `stubs/ap_config.h`:
`AP_SIM_ENABLED 1`, `HAL_WITH_SPI 1`, `HAL_WITH_RAMTRON 1`, `AP_OPENDRONEID_ENABLED 1`,
`AP_SIGNED_FIRMWARE 0`, `AP_NOTIFY_LP5562_BUS 2`, `AP_NOTIFY_LP5562_ADDR 0x30`, `_GNU_SOURCE 1`.
`HAL_PROGRAM_SIZE_LIMIT_KB` keeps its SITL default 4096 (`board/sitl.h`).

Flags: `-std=gnu++11 -O2 -ffp-contract=off -fno-fast-math -ftrapping-math -fsigned-char
-fno-exceptions -fno-rtti` and, for clang, `-cl-single-precision-constant` (waf's clang flag,
`boards.py:403, :512`; GCC: `-fsingle-precision-constant`, `:410, :521`). waf uses `-O3` for SITL; neither level
changes floating-point semantics here. Include order: `stubs/`, `libraries/AP_Common/missing`,
`libraries/`, `-include ap_config.h`.

## Harness (`main.cpp`)

Mirrors the Lean harness, `Copter/Loop.lean`, `Copter/ModeAuto.lean`, `Copter/AutoYaw.lean`,
`Copter/Main.lean`:

- Construction as `ArduCopter/system.cpp:387, :454, :467, :479` (`AP_MotorsMatrix(400)`, the view,
  `AC_AttitudeControl_Multi`, `AC_PosControl`), zero-filled; `AP_MotorsMatrix::init(QUAD, X)`;
  armed, interlocked, desired and current spool state `THROTTLE_UNLIMITED` (the `AP_Motors` port's
  environment assumption; `_spool_state` is set through a harness subclass).
- Parameters: the defaults of the real `var_info` tables (via each constructor's
  `setup_object_defaults`), then the port's run deviations (`Copter/Parameters.lean` `defaults`:
  `ATC_RAT_YAW_P 0.3`, `ATC_RAT_YAW_I 0.02`, `MOT_HOVER_LEARN 0`, `MOT_THST_HOVER 0.39`,
  `MOT_BAT_VOLT_MAX 0`), then the override files, set by name through the tables (`ATC_`, `PSC`,
  `MOT_` prefixes of `ArduCopter/Parameters.cpp`). `WP_*`, `WP_YAW_BEHAVIOR`, `PILOT_Y_RATE_TC`,
  `ACRO_RP_RATE_TC`, `run.*` are harness values. All 107 parameters both sides print agree
  exactly (`--print-params` against `copter --print-params`); the `*_NTF`/`*_NEF` notch indices do
  not exist with `AP_FILTER_ENABLED 0`.
- Input parsing as `Copter/Main.lean`: position by `strtod`, the rest by `strtof` (each decimal
  rounded once), `dt` to whole microseconds, half up, from the exact decimal.
- Takeover on the first sample: view of the sample, `relax_attitude_controllers()`,
  `set_throttle_out(get_throttle_hover(), true, POSCONTROL_THROTTLE_CUTOFF_FREQ_HZ)`, the throttle
  filter reset to `_throttle_in`.
- Per tick, in the fast-task order: tick counter +1 and loop time (`1/400` on the first tick, else
  `float(dt_us) * 1e-6f`); the gyro; `set_dt_s` on both controllers and the motors,
  `rate_controller_run()`, `rate_controller_target_reset()`; `motors->output()` (the actuators are
  read here); the rest of the sample and `view.update()`; `update_estimates(false)`; on the first
  tick `ModeAuto::init`'s `wp_and_spline_init_m` calls into `AC_PosControl`
  (`D_init_controller_stopping_point`, `NE_init_controller_stopping_point`,
  `NE_set_max_speed_accel_m`, `NE_set_correction_speed_accel_m`, `D_set_max_speed_accel_m`,
  `D_set_correction_speed_accel_m`, `AC_WPNav.cpp:223-235`) and the rate time constants; AutoYaw
  HOLD from `--hold-from`; then `wp_run`: `set_pos_terrain_target_D_m(0)`,
  `set_pos_vel_accel_NED_m(trace position, velocity, acceleration)`, `NE_update_controller()`,
  `D_update_controller()`, the AutoYaw heading (`LOOK_AT_NEXT_WP`: `pos_control->get_yaw_rad()`,
  `get_yaw_rate_rads()`, `Angle_And_Rate`; `HOLD`: the attitude target's yaw, rate 0,
  `Rate_Only`), `input_thrust_vector_heading(get_thrust_vector(), heading)`.
- The navigator's outputs come from the port's trace, which records the target after the tick.
  That is what `AC_WPNav` sent unless `AC_P_2D/AC_P_1D::update_all` clamped the position error
  (`AC_P_2D.cpp:32-34`, `AC_P_1D.cpp:32-38`); the harness counts the ticks on which the clamp fires
  on the fed value: none on the recorded flight, so the fed targets are exactly the navigator's.
- `--vehicle-calls` adds the three ArduCopter calls that the Lean harness omits as no-ops:
  `attitude_control->landed_gain_reduction(false)` and `pos_control->set_reset_handling_method(...)`
  (`mode.cpp:507-510`), `motors->set_desired_spool_state(THROTTLE_UNLIMITED)`
  (`mode_auto.cpp:1143`). The output is byte-identical with and without them.
