# The reference vehicle (Phase 0 of PORT-PLAN.md)

`build/reference/copter_ref` is the reduced ArduCopter of PORT-PLAN.md appendix A, built from the unmodified ArduPilot sources at 802db19de1 for the SITL board, with a lock-step HAL in place of `libraries/AP_HAL_SITL` and stand-ins for the four SITL sensor back ends and `SITL::SIM`. It reads one input line per 400 Hz step and writes one output line per input line. Every later phase is tested against it: the same input lines must give the same output lines, bit for bit.

## Build

```
reference/prepare.sh        # once: build copy + waf configure + waf build (about 1 min at -j4)
python3 reference/build.py  # the reference vehicle (about 4 min from scratch at -j4, incremental after)
```

- `reference/prepare.sh` makes `build/reference/ap`, an APFS clone (`cp -c`) of `build/survey/ap-min` (the pinned checkout with its submodules) restored to 802db19de1, applies `reference/patches/*.patch` (one: the `#ifndef` guard around `HAL_SOLO_GIMBAL_ENABLED` in `AP_HAL/board/sitl.h`, PORT-PLAN.md 2.3), and runs waf (`--board sitl --disable-networking --extra-hwdef=reference/cfg/ref.hwdef`). waf's build provides the generated MAVLink headers (ArduPilot's fork e03dad40), `ap_config.h`, `hwdef.h` and `compile_commands.json`. The ArduPilot checkout is never touched.
- `reference/cfg/ref.hwdef` is appendix A (143 defines) plus `AP_BATTERY_ANALOG_ENABLED 1` (D8).
- `reference/build.py` compiles every C++ unit of ArduCopter and `libraries/` in waf's copter build with waf's own defines and include paths, minus `-O`/`-g`, plus the reference flags `-O2 -ffp-contract=off -fno-fast-math -fno-builtin-sinf -fno-builtin-cosf -fno-builtin-sin -fno-builtin-cos -fno-builtin` (waf already passes `-std=gnu++11 -cl-single-precision-constant -ftrapping-math -fno-slp-vectorize`), with `reference/hal` first on the include path. Excluded: `libraries/AP_HAL_SITL`, `libraries/SITL` (the simulator), `AP_InertialSensor_SITL.cpp`, `AP_Baro_SITL.cpp`, `AP_Compass_SITL.cpp`, `AP_GPS_SITL.cpp`, and three simulation consumers that read the real `SITL::SIM` (`AP_HAL/SIMState.cpp`, `AP_IRLock_SITL*.cpp`). Linked as waf links (vehicle objects, the libraries as a static archive, `-Wl,-dead_strip,-ld_classic`).
- Math library: musl 1.2.5's sources in `libm/` (the copy the Lean side translates; read only here), the files of `libm/musl_files.txt`, compiled as `libm/build_musl.sh` compiles them (C99, the reference flags, every name prefixed `cpp2lean_musl_` by `libm/env/musl_prefix.h`) into `build/reference/libm`, and bound to the C names at link time (`-Wl,-alias`). The vehicle needs no function beyond that list (`reference/libm_extra.txt` is empty); `build.py` prints the math functions still imported from the platform: none. From the platform's C library the vehicle still calls `snprintf`, `printf`, `vprintf`, `asprintf` (formatting, D10), `strtof` (AP_Param), `nanf` (the constant `NaNf` of `AP_Math.h`), `random` (AP_Math's `rand_float` on the SITL board, and AP_AHRS's loop jitter, which is off), the string functions, `calloc`/`free`, and the POSIX file functions of `AP_Filesystem_posix` (none is called in the runs below: no file appears).

What replaces what (`reference/hal`):

| file | replaces | what it does |
|---|---|---|
| `lockstep.cpp`, `lockstep.h` | `libraries/AP_HAL_SITL` (HAL class, Scheduler, UART, Storage, RCInput, RCOutput, AnalogIn, Util, `system.cpp`) | the lock-step HAL below; GPIO, I2C, SPI, WSPI, optical flow, flash are `AP_HAL_Empty`'s |
| `sensors.cpp`, `sensors_ins.cpp`, `sensors_baro.cpp`, `sensors_compass.cpp`, `sensors_gps.cpp` | `SITL::SIM`, `AP_InertialSensor_SITL.cpp`, `AP_Baro_SITL.cpp`, `AP_Compass_SITL.cpp`, `AP_GPS_SITL.cpp` | the back ends, with ArduPilot's class declarations, calling the front ends where the SITL back ends do; one file per sensor (Phase 3), reading the step's record through `est_input.h`, so that the same sources are translated with the front ends |
| `est_input.h` | (nothing: an addition) | Phase 3: the record of one line (`EstRecord`, IMU samples flat) and the accessors the stand-ins read it through (`est_input()`, the step period, the IMU rate, the GPS latch), which `lockstep.cpp` defines from the parsed line and `est_scheduler.cpp` from its current record; `est_event`, the stand-ins' events for the estimation output |
| `SITL/SITL.h` | `libraries/SITL/SITL.h` | `SITL::SIM` with only the members code outside the simulator reads, constants, and an empty `var_info` (no `SIM_*` parameters, D2) |
| `SITL/SIM_GPS.h`, `SITL/SIM_Compass.h` | the simulator's headers that `AP_GPS.h` and `AP_Compass_SITL.h` include | empty / a member-only `CompassSim` |
| `AP_HAL_SITL/Semaphores.h` | the SITL semaphores (`board/sitl.h` includes them for `HAL_Semaphore`) | no-op semaphores (one thread, PORT-PLAN.md 4.11) |
| `AP_HAL_SITL/CANSocketIface.h` | SITL's CAN interface (`AP_CANManager.cpp` includes it; SITL has `HAL_NUM_CAN_IFACES 2`) | a class that exists and is never allocated (no `CAN_Pn_DRIVER`) |
| `AP_HAL/SIMState.h` | the on-hardware simulator header (`AP_Scheduler.cpp` includes it) | the class declaration only |
| `est_probe.cpp` | (nothing: an addition) | the estimation output of `--est`; compiled with `-fno-access-control` (it reads private members), the only file with that flag |
| `est_scheduler.cpp`, `est_scheduler.h` | (nothing: translation only) | Phase 3: the HAL scheduler of the estimator's translation (lockstep.cpp's scheduler logic over input records held by the object, PORT-PLAN.md "Phase 3:" decision on delays; the GPS latch; the stand-ins' events per consumed line; the difftest's `feed_line`, `feed_baro_lines`); not compiled into copter_ref (`build.py` compiles `HAL_SOURCES` only) |

## Running

```
copter_ref [--storage IMAGE] [--storage-out IMAGE] [--imus N] [--imu-rate HZ] [--timing] [--timing-file F] [--profile F] [--est F] < inputs > outputs
```

- `--storage IMAGE` boots from a storage image (`HAL_STORAGE_SIZE` = 16384 bytes on this board); without it the storage starts zeroed (AP_Param then formats it). `--storage-out IMAGE` writes the storage at the end (D12).
- `--imus N` (1 or 2, default 1, D5) is `SITL::SIM::imu_count`; `--imu-rate HZ` (default 1200) the sample rate the IMU stand-in registers.
- `--timing`, `--timing-file F`: wall time of the vehicle per step (measurement only; never read by the vehicle). `--profile F`: a sampling thread attributes wall time to the scheduler task running (`persistent_data.scheduler_task`) or to the HAL's phases, appended to F.
- `--est F`: the estimation output, one line per step into F (section "Estimation output (Phase 3)" below; reads only, the protocol output is unchanged).
- The run ends at end of input (exit 0), on a reboot request (exit 4), on `AP_HAL::panic` (exit 3, message on stderr) or on a malformed line (exit 2). Anything the vehicle prints with `printf` goes to stderr; stdout carries only the protocol.

## Protocol

One input line per step, one output line per input line, flushed. Every floating-point value is the hexadecimal bit pattern of a binary32 (8 digits) or binary64 (16 digits), big-endian digit order (`struct.pack(">f")`), so a line denotes one set of bits and a recorded file is the bit-level trace of everything that crosses the boundary (this is the `--bits` of the earlier protocol, always on). `sim/lockstep_proto.py` encodes and decodes; `lockstep_proto.py decode FILE` prints a trace in decimal with the MAVLink messages named.

Input (tokens in this order, all but `t=` optional):

```
t=<us> imu0=<ax>,<ay>,<az>,<gx>,<gy>,<gz>[;<sample>...] [imu1=...] baro=<Pa>,<degC> mag=<x>,<y>,<z>
       gps=<lat>,<lon>,<alt>,<vn>,<ve>,<vd> rc=<pwm1>,...,<pwm16> bat=<V>,<A> up=<hex bytes>
```

| token | meaning | type | stand-in |
|---|---|---|---|
| `t` | time of this step, µs, strictly increasing (2500 µs steps) | decimal | the clock: `AP_HAL::micros64()` returns it until the next line |
| `imu0`, `imu1` | k samples of IMU i over the step, oldest first: body-frame (FRD) specific force m/s², body rates rad/s | binary32 | each sample through `_notify_new_*_sensor_rate_sample`, `_rotate_and_correct_*`, `_notify_new_*_raw_sample(…, t − (k−1−j)·Δt/k)`, accel before gyro; temperature 20 °C |
| `baro` | pressure (Pa), temperature (°C) | binary32 | latched by the back end's timer process, copied to the front end in `update()` |
| `mag` | body-frame field as the sensor reports it (mGauss; the front end adds `COMPASS_OFS`, which the stand-in sets to SITL's (5, 13, −18)) | binary32 | `accumulate_sample(field, 10)` in the timer process |
| `gps` | latitude, longitude (deg), altitude AMSL (m), NED velocity (m/s) | binary64 | latched until the next `AP_GPS_SITL::read`, which fills `state` as SITL's does (`int32_t(lat*1e7)`, altitude through `float`, 15 satellites, HDOP 1.00, `FIX_3D`, GPS time from 2026-01-01T00:00:00Z plus the clock) |
| `rc` | a new RC frame: 16 PWM values | decimal | `RCInput::new_input()` true once per frame (D7); no frame for long enough is the RC failsafe |
| `bat` | battery voltage (V), current (A); kept until the next `bat` | binary32 | SITL's analog pins 13 (V/10.1) and 12 (A/17) |
| `up` | the MAVLink bytes received since the previous line (UDP datagrams concatenated) | hex | appended to SERIAL0's receive queue (16384 bytes) |

Output:

```
t=<us> pwm=<ch1>,...,<ch16> [down=<hex bytes>]
```

`pwm`: the 16 RC output channels as last pushed (SITL's `RCOutput`: zero while the safety switch is engaged). `down`: everything written to SERIAL0 (MAVLink and the console, which is SERIAL0 as in SITL) since the previous output line.

Semantics of a step (SITL's lock-step semantics, PORT-PLAN.md 3.1): the vehicle runs until it waits (`delay`, `delay_microseconds`, `AP_InertialSensor::wait_for_sample` through `delay_microseconds_boost`); every wait consumes input lines until the requested time has passed. Consuming line k: write output line k−1, read line k, set the clock, append `up` to the receive queue, take the RC frame and the GPS record, run the timer processes (the sensor back ends), the timer failsafe and the IO processes (`HALSITL::Scheduler::timer_event`). After every `loop()` the IO processes run again (`HAL_SITL::run`). In flight one line is one scheduler loop.

## Trace format and the replay oracle

A run is `inputs.txt` (the lines sent), `outputs.txt` (the lines received) and `storage_in.bin` (the boot image, when there is one). The oracle: `copter_ref --storage storage_in.bin < inputs.txt` reproduces `outputs.txt` byte for byte. The simulator, the ground station and the wall clock are outside the trace, so any session (scripted or QGroundControl) is replayable without them.

## Harness (sim/)

- `sim/fly_reference.py` flies the vehicle in gym-pybullet-drones (CtrlAviary, CF2X, PYB physics at 1200 Hz; environment, frames and motor map from `sim/run_copter.py`), one protocol line per 400 Hz step, PWM 1000..2000 mapped linearly to the thrust fraction. Sensor layer: IMU after every physics substep (3 per line), barometer and compass every 4th line (100 Hz), GPS every 80th (5 Hz), RC every 8th (50 Hz, sticks neutral, throttle 1000, mode switch low), battery 12.6 V / 0.5 A. Barometer: ArduPilot's 1976 atmosphere; compass: ArduPilot's field at CMAC (`AP_Declination` tables, `build/reference/magfield`) rotated into the body frame; GPS: NED position about CMAC (−35.363261, 149.165230, 584 m) with ArduPilot's `LOCATION_SCALING_FACTOR`. `--seed N` adds Gaussian noise from `numpy.random.default_rng(N)` (accel 0.05 m/s², gyro 0.002 rad/s, baro 1 Pa, mag 2 mGauss, GPS 0.1 m and 0.05 m/s). Ground station: `--script image` (blank storage: download the parameters, `PARAM_SET` the overrides of `--params`, write the image), `--script flight` (`sim/lockstep_gcs.py`, below), or `--udp` (real time, SERIAL0 bridged to UDP 127.0.0.1:14550). `--replay-check` replays the trace after the run.
- `sim/lockstep_gcs.py`: a scripted ground station inside the lock step (pymavlink built from ArduPilot's pinned submodule, ArduPilot's dialect; system 255/190): heartbeat 1 Hz, stream request, parameter download (`PARAM_REQUEST_LIST`, then `PARAM_REQUEST_READ` for missing indices), mission upload and download, `DO_SET_MODE`, arming, `NAV_TAKEOFF`.
- `sim/run_qgc_reference.py`: one session of the installed QGroundControl against `fly_reference.py --udp`, observed through QGroundControl's console log only (procedure of leanfc's `sim/mavlink/run_qgc.py`).
- `sim/params/reference-cf2x.txt`: the overrides written into the image (frame, `GPS1_TYPE 100`, `BATT_MONITOR 4`, accelerometer offsets, the CF2X motor and gain settings of `copter-cf2x*.txt`, `WP_SPD 2`).
- Python: `build/reference/venv` (Python 3.12, `pymavlink` installed from `build/reference/ap/modules/mavlink/pymavlink` with `MDEF` = the pinned message definitions, and a `.pth` to `sim/.venv`'s packages; `sim/.venv` itself is unchanged).

Commands of the Phase 0 runs:

```
V=build/reference/venv/bin/python
$V sim/fly_reference.py --script image --params sim/params/reference-cf2x.txt \
   --storage-out build/reference/storage-cf2x.bin --out sim/out/lockstep-image --duration 60
$V sim/fly_reference.py --script flight --storage build/reference/storage-cf2x.bin --out sim/out/lockstep-flight --replay-check
$V sim/fly_reference.py --script flight --storage build/reference/storage-cf2x.bin --seed 1 --out sim/out/lockstep-flight-noisy --replay-check
$V sim/run_qgc_reference.py --seconds 120 --out sim/out/lockstep-qgc
python3 reference/profile.py sim/out/lockstep-flight --runs 5 --flight-from 42.03 --flight-to 88.03
```

## Phase 0 results (2026-11-11, macOS arm64, Apple clang 17)

Flights (both: boot from the image, EKF3 initializes from the simulated sensors, 781 parameters downloaded in 16.7 s simulated, "EKF3 IMU0 is using GPS" at 41.8 s, a 6-item mission uploaded and downloaded back, GUIDED, armed, `NAV_TAKEOFF` 5 m, AUTO: takeoff, waypoint (10, 0), waypoint (10, 10), spline waypoint (0, 10), land at home; disarmed by the vehicle at 87.2 s; 36,013 steps, 90 s simulated in 4.7 to 4.9 s wall, about 19 times real time):

| run | trace | replay |
|---|---|---|
| image (blank storage, 29 parameters set) | `sim/out/lockstep-image` (8,555 steps) | identical |
| deterministic flight | `sim/out/lockstep-flight` | identical, 36,013 lines |
| noisy flight (`--seed 1`) | `sim/out/lockstep-flight-noisy` | identical, 36,013 lines |
| QGroundControl session (real time) | `sim/out/lockstep-qgc/harness` | identical, 55,515 lines |

Speed (`reference/profile.py` on the deterministic flight, median of 5 replays; vehicle time per step, without the protocol's parsing and printing; the whole replay process takes 5.5 µs per step):

| part of the trace | steps | mean µs | p50 µs | p99 µs | max µs |
|---|---|---|---|---|---|
| all | 36,013 | 3.40 | 3.33 | 8.92 | 93.25 |
| before arming | 16,812 | 2.89 | 2.62 | 7.38 | 93.25 |
| armed, flying | 18,400 | 3.86 | 3.42 | 9.12 | 13.00 |

Per task (sampled wall time, µs per step averaged over the flight): protocol parsing and printing 2.60; `Copter::read_AHRS` (AHRS + EKF3, one double-precision core) 0.69; `Copter::update_flight_mode` (the modes, position and attitude controllers) 0.59; `GCS::update_send` 0.25; scheduler bookkeeping 0.19; sensor back ends (timer processes) 0.16; `GCS::update_receive` 0.13; land and crash detectors 0.12; `rc_loop` 0.11; `motors_output` 0.10; `AP_InertialSensor::update` 0.07; rate controller 0.07; everything else below 0.07 each (full table: `build/reference/profile-flight.md`). The 400 Hz budget is 2,500 µs per step: a Lean vehicle up to about 700 times slower than this C++ build is still real time.

QGroundControl 5.1.5 (none was running; one instance started and terminated by `run_qgc_reference.py`): connected 3.6 s after start ("Adding new vehicle … UDP Link (AutoConnect)"), tried MAVLink FTP for the parameters (two `Open File RO` timeouts: FTP is compiled out), fell back to the parameter protocol, "Initial load complete" at 31.4 s, mission download (count 1), "Signalling initialConnectComplete" at 31.4 s. Its log also has warnings about its own bundled parameter metadata (`EK3_BCN_DELAY` and others: defaults outside the metadata's range), printed at 1.4 s, before any vehicle connected.

## Estimation output (Phase 3)

`copter_ref --est FILE` writes the reference side of PORT-PLAN.md's oracle (b), the estimator replay: per protocol step, the outputs of AP_AHRS and EKF3 to compare with the translated estimator, and the inputs that the rest of the vehicle gives the estimator, so that a replay harness can drive the translated sensor front ends, AP_DAL, EKF3 and AP_AHRS with the recorded sensor lines and make the same vehicle-side calls. `reference/hal/est_probe.cpp` (hooked into `lockstep.cpp`'s `step()`) only reads: const getters and data members, no ArduPilot function that changes state; it reads private members, so `reference/build.py` compiles that one file with `-fno-access-control` (no ArduPilot file changes).

### When a line is written

One line per input line, written right after that step's output line, i.e. when the vehicle next waits and the next input line is consumed (or at end of input): the state *after* the vehicle has run for the step. Structure of the steps in the two flights (`init` and `in` below): boot-time init consumes lines 1 to 915 inside `delay`s of `setup()` (773 of them with delay callbacks, `dcb`); from then on every step is exactly one main loop: the line is consumed in the `delay_microseconds(1)` at the end of `AP_Scheduler::loop` (SITL's "move micros forward", `in=-1`), the HAL runs the timer processes (the sensor stand-ins) and IO processes, the rest of that `loop()` and `HAL_SITL::run`'s IO processes run, then the next `loop()`: `wait_for_sample` (no wait: the clock is already ahead), `tick()` (one per step, `tick` below), the tasks (`tasks` below), and its `delay_microseconds(1)` ends the step. The last init line (915, t = 2.2875 s) is the step in which `setup()` returned and the first `loop()` ran (tick 1).

### Line format

```
t=<us> init=<b> in=<i> dcb=<n> tick=<n> tasks=<i,...|-> armed=<b> flying=<b>,<ms> tkd=<b>,<ms>,<b>,<ms> thgt=<n>
  home=<set>,<locked>,<lat>,<lng>,<alt>,<frame> cfg=<class>,<fly_fwd>,<ekf_type>,<srcset>,<trim x,y,z>
  comp=<thr>,<volt> bgnd=<n>,<p0>...,<drift> q=<ok>,<w>,<x>,<y>,<z> rpy=<r>,<p>,<y> dcm=<9> vel=<ok>,<n>,<e>,<d>
  pos=<ok>,<n>,<e>,<d> loc=<ok>,<lat>,<lng>,<alt>,<frame> gyro=<3> accef=<3> resets=<att>,<yaw>,<ne>,<d>
  healthy=<b> initialised=<b> origin=<ok>,<lat>,<lng>,<alt>,<frame> ekf=<type> fs=<ok>,<hex32>
  primary=<i> ncores=<n> gbias=<3> abias=<3> var=<ok>,<vel>,<pos>,<hgt>,<mx>,<my>,<mz>,<tas>,<offx>,<offy>
  c<k>.x=<24 doubles> c<k>.fs=<hex32>,<b> c<k>.P=<fnv> c<k>.out=<fnv> c<k>.imu=<fnv> c<k>.var=<ok>,<7 floats>
  c<k>.gsf=<ok>,<yaw>,<yawvar>,<nclips>,<fnv>     (one line; the c<k>. keys for every EKF3 core k)
  baro=<n>[,<healthy>,<pressure>,<temperature>,<altitude>,<ground pressure>,<last update ms>]
  mag=<n>[,<healthy>,<field x,y,z>,<last update us>,<offsets x,y,z>,<dev id>] ev=<events>
```

Floats and doubles are hexadecimal bit patterns as in the protocol (8 digits binary32, 16 digits binary64); `<b>` is 0/1; integers are decimal; `<hex32>` is a flag word; `<fnv>` a 64-bit FNV-1a digest (16 hex digits). The keys from `gbias` on are absent while EKF3 has no cores (`ncores=0`, before `InitialiseFilter`); `tick`/`tasks` are absent while the scheduler has no task table. The first line of the file is `# tasks <i>=<name>@<priority> ...`, the scheduler's merged task table (AP_Scheduler::run's order; `*` marks the fast tasks): in these flights 0..9 are the fast tasks `AP_InertialSensor::update`, `run_rate_controller_main`, `motors_output_main`, `read_AHRS`, `read_inertia`, `check_ekf_reset`, `update_flight_mode`, `update_home_from_EKF`, `update_land_and_crash_detectors`, `update_rangefinder_terrain_offset`, then 10 `rc_loop`, 11 `throttle_loop`, 12 `AP_GPS::update`, 13 `update_batt_compass`, 14 `read_aux_all`, 15 `auto_disarm_check`, 16 `update_altitude`, 17 `run_nav_updates`, 18 `update_throttle_hover`, 19 `three_hz_loop`, 20 `AP_Notify::update`, 21 `one_hz_loop`, 22 `ekf_check`, 23 `check_vibration`, 24 `gpsglitch_check`, 25 `takeoff_check`, 26 `standby_update`, 27 `lost_vehicle_check`, 28 `GCS::update_receive`, 29 `GCS::update_send`, 30 `AP_InertialSensor::periodic`, 31 `send_watchdog_reset_statustext`, 32 `AP_Vehicle::one_Hz_update`, 33 `AP_Vehicle::update_arming`.

Step and inputs (vehicle side; every value is the state after the step):

| key | content |
|---|---|
| `t` | the step's time (µs), as in the output line |
| `init` | 1: this step's input line was consumed during boot-time init (inside a `delay` of `setup()`, before the main loop: `AP_HAL::Scheduler::is_system_initialized()` false) |
| `in` | `AP_HAL::Util::persistent_data.scheduler_task` when the line was consumed (−1 between tasks/end of loop, −3 in `wait_for_sample`, ≥ 0 inside that task; meaningless while `init=1`, where it is the initial 0) |
| `dcb` | delay callbacks (`AP_Vehicle::scheduler_delay_callback`: GCS, notify) run during the step (only in init) |
| `tick` | `AP_Scheduler::_tick_counter32` |
| `tasks` | the scheduler tasks that ran in the step, in execution order (indices of the `# tasks` table; `-`: none): task i ran iff the tick advanced and its private `_last_run[i]` changed or equals the 16-bit tick counter |
| `armed` | `hal.util->get_soft_armed()` |
| `flying` | `AP_Vehicle::likely_flying`, `_last_flying_ms` (AP_DAL's `time_flying_ms` = millis − `_last_flying_ms` while flying; compass learning reads it too) |
| `tkd` | AP_AHRS `takeoff_expected`, `takeoff_expected_start_ms`, `touchdown_expected`, `touchdown_expected_start_ms` |
| `thgt` | AP_AHRS `terrainHgtStableState` (0 false, 1 true, 3 unknown) |
| `home` | `home_is_set()`, `home_is_locked()`, `get_home()` (lat, lng 1e-7 deg, alt cm, `Location::AltFrame`) |
| `cfg` | `get_vehicle_class()`, `get_fly_forward()`, `configured_ekf_type()`, `get_posvelyaw_source_set()`, `get_trim()` |
| `comp` | Compass `_thr` (`set_throttle`), `_per_motor.voltage` (`set_voltage`) |
| `bgnd` | AP_Baro `num_instances()`, `get_ground_pressure(i)` per instance, `get_baro_drift_offset()` |

Outputs:

| key | content |
|---|---|
| `q` | `AP_AHRS::get_quaternion` (bool, then q1..q4 = w, x, y, z) |
| `rpy`, `dcm` | `get_roll_rad`, `get_pitch_rad`, `get_yaw_rad`; `get_rotation_body_to_ned` rows a, b, c |
| `vel`, `pos`, `loc` | `get_velocity_NED`, `get_relative_position_NED_origin` (`Vector3p`: doubles), `get_location`, each with its bool |
| `gyro`, `accef`, `resets` | `get_gyro`, `get_accel_ef`; attitude, yaw, NE and D reset counts |
| `healthy`, `initialised`, `origin`, `ekf`, `fs` | `healthy()`, `initialised()`, `get_origin` (bool, location), `active_EKF_type()` (0 DCM, 3 EKF3), `get_filter_status_for_configured_backend` (bool, `nav_filter_status::value`) |
| `primary`, `ncores` | `NavEKF3::getPrimaryCoreIndex()`, number of cores |
| `gbias`, `abias`, `var` | `NavEKF3::getGyroBias(-1)`, `getAccelBias(-1)` (primary core), `getVariances` (bool, velocity, position, height, magnetometer x/y/z, airspeed test ratios, offset x/y) |
| `c<k>.x` | core k's `statesArray[0..23]` (quaternion, velocity, position, gyro bias, accel bias, earth field, body field, wind) |
| `c<k>.fs` | core k's `getFilterStatus` value, `statesInitialised` |
| `c<k>.P` | digest of `Pmut[i][j]`, row-major |
| `c<k>.out` | digest of the output predictor: `outputDataNew`, `outputDataDelayed` (quat q1..q4, velocity, position each), `delAngCorrection`, `velErrintegral`, `posErrintegral`, `vertCompFiltState` pos, vel, acc, then `storedOutput`'s `_size`, `_oldest`, `_youngest`, `_filled` and its `_size` elements by buffer index |
| `c<k>.imu` | digest of `storedIMU`: `_size`, `_oldest`, `_youngest`, `_filled`, then per buffer index `delAng`, `delVel`, `delAngDT`, `delVelDT`, `time_ms`, `gyro_index`, `accel_index` |
| `c<k>.var` | core k's `getVariances` (bool and the first 7 values) |
| `c<k>.gsf` | core k's `EKFGSF_yaw::getYawData` (bool, yaw, yaw variance, n_clips) and a digest of the whole bank: `delta_angle`, `delta_velocity`, `angle_dt`, `velocity_dt`; per model `AHRS[m]`: `R` rows a, b, c, `gyro_bias`, `aligned`, `accel_FR[2]`, `vel_NE[2]`, `fuse_gps`, `accel_dt`; `ahrs_tilt_aligned`, `accel_gain`, `ahrs_accel`, `ahrs_accel_norm`, `true_airspeed`; per model `EKF[m]`: `X[3]`, `P[3][3]`, `S[2][2]`, `innov[2]`; `vel_fuse_running`, `run_ekf_gsf`, `GSF.yaw`, `GSF.yaw_variance`, `GSF.weights[]`, `n_clips` |

Front ends (Phase 3, sensor front ends; README.md "Phase 3: sensor front ends and AP_Param"): `baro` is AP_Baro's
`num_instances()` and, for instance 0, `healthy(0)`, `get_pressure(0)`, `get_temperature(0)`, `get_altitude(0)`,
`get_ground_pressure(0)`, `get_last_update(0)`; `mag` is Compass's `get_count()` and, for instance 0, `healthy(0)`,
`get_field(0)`, `last_update_usec(0)`, `get_offsets(0)`, the dev id; `ev` the events of the step's sensor stand-ins
(`reference/hal/est_input.h`: 1 AP_Baro_SITL constructed in `AP_Baro::init`, 2 its `update` run by `AP_Baro::update`
(also inside `AP_Baro::calibrate`), 4 AP_Compass_SITL constructed in `Compass::init`). Before the first line, `# params
name=value ...` lists AP_Baro's and Compass's parameters as the vehicle holds them at the first consumed line (after
`AP_Param::load_all`, before the front ends' init; floats as bit patterns, integers in decimal); since the estimator World
(README.md "Phase 3: the estimator World and the EKF3 replay") also AP_InertialSensor's and AP_GPS's, and NavEKF3's
(`EKF3.<member>` for every entry of its `var_info` and `var_info2`, in table order) with its source selection's
(`EKF3.sources._source_set[i].posxy` ... `.yaw`, `EKF3.sources._options`): every parameter the estimator World holds, 261;
since the estimator World with AP_AHRS (README.md "Phase 3: AP_AHRS in the estimator World, the full estimation replay")
also AP_AHRS's 14 `var_info` entries in table order (`ahrs.gps_gain`, `ahrs._gps_use`, `ahrs._kp_yaw`, `ahrs._kp`,
`ahrs._wind_max`, `ahrs._trim.x/.y/.z`, `ahrs._board_orientation`, `ahrs.beta`, `ahrs._gps_minsats`, `ahrs._ekf_type`,
`ahrs._options`, `ahrs._origin_lat/_lon/_alt`; DCM's parameters are references to these): 277. These keys come at the
end of each line and after the task table's header; every earlier key is unchanged, and the protocol output too
(`cmp` of both recorded flights' outputs; `est.txt`'s earlier keys identical on all 36,013 lines). The last key of each
line, `cin=<throttle>,<voltage>`, is the vehicle's arguments of `Compass::set_throttle` and `set_voltage` in
`Copter::update_batt_compass` (task 13: `motors->get_throttle()`, `battery.voltage()` after `battery.read()`; neither
changes later in the step), the compass's two inputs from outside the estimator (`comp=` is the compass's state after
them: `set_voltage` low-passes its argument). `reference/tools/est_compare.py A B --keys-of-a` compares only the keys of
A's lines (an older trace A against a newer B).

Digests: FNV-1a 64 (offset basis 0xcbf29ce484222325, prime 0x100000001b3) over the listed values in the listed order, each value as its bit pattern in little-endian bytes of its width (double 8, float 4, `uint32_t` 4, `uint8_t` 1, bool 1 byte 0/1; vectors x, y, z). `ftype` is double in this build (`HAL_WITH_EKF_DOUBLE`).

### Inputs from the rest of the vehicle

Calls into AP_AHRS, AP_DAL, NavEKF3, AP_InertialSensor, AP_Baro, AP_Compass and AP_GPS from outside these libraries that change their state (grep of `ArduCopter/`, `AP_Vehicle`, `AP_Arming`, `GCS_MAVLink`, `AP_Scheduler`, `AP_GroundEffect`, `AP_Motors`, `AC_*`, `AP_Mission`, `RC_Channel`, `AP_Notify` for `ahrs.`, `AP::ahrs()`, `ins.`, `AP::ins()`, `barometer.`, `AP::baro()`, `compass.`, `AP::compass()`, `gps.`, `AP::gps()`, `AP::dal()`, `EKF3`; nothing outside calls AP_DAL or NavEKF3 directly), and what the estimator reads back from the vehicle:

| call (caller) | when, in the flights | token |
|---|---|---|
| `ins.init`, `barometer.init`/`calibrate`, `compass.init`, `gps.init`, `ahrs.init`, `ahrs.set_vehicle_class(COPTER)`, `ahrs.reset()` (`Copter::init_ardupilot`) | boot, `init=1` (the class at t = 1.76 s) | `cfg`, `bgnd` |
| `AP_InertialSensor::update` (fast task 0), `ahrs.update(true)` (`read_AHRS`, fast task 3; runs EKF3 through AP_DAL), `AP_GPS::update` (task 12), `compass.read` (task 13), `barometer.update` (`update_altitude`, task 16), `AP_InertialSensor::periodic` (task 30), `AP::ins().wait_for_sample` (scheduler) | every step / at their rates | `tasks` |
| `compass.set_throttle`, `compass.set_voltage` (`update_batt_compass`, task 13, right before `compass.read`) | 10 Hz; `_thr` stays 0 (only with throttle motor compensation), the voltage follows the battery | `comp` |
| `ahrs.set_terrain_hgt_stable` (`update_ekf_terrain_height_stable` in `throttle_loop`, task 11; forwarded to `EKF3.setTerrainHgtStable`) | 3 → 0 at the first `throttle_loop` (2.305 s); 1 from takeoff (42.0 s) to 49.5 s and from the landing approach (74.7 s) | `thgt` |
| `ahrs.set_home`, `ahrs.lock_home` (`update_home_from_EKF`, fast task 7, once the EKF has an origin; `set_home_to_current_location` at arming in `GCS::update_receive`, task 28) | 14.41 s; again at arming 41.86 s (not locked) | `home` |
| `hal.util->set_soft_armed` (`AP_Arming_Copter::arm` from the `COMPONENT_ARM_DISARM` command, task 28; `disarm` from AUTO's land completion, `ModeAuto` in `update_flight_mode`, fast task 6) | 41.855 s armed, 87.2 s disarmed | `armed` |
| `set_likely_flying` (`Copter::set_land_complete`, from the land detector, fast task 8, the takeoff and modes) | 45.27 s flying, 86.7 s landed | `flying` |
| `ahrs.resetHeightDatum` (arming without home), `ahrs.set_origin` (`SET_GPS_GLOBAL_ORIGIN`), `AP::baro().update_calibration` (`PREFLIGHT_CALIBRATION`), `ahrs.request_yaw_reset`/`check_lane_switch` (`ekf_check` on a failure), `ahrs.set_posvelyaw_source_set` (RC aux), `ahrs.set_trim`/`add_trim`, `compass.set_declination` (tuning), `AP::gps().prepare_for_arming` (nothing for the SITL back end) | not in these flights (the home is set before arming; no failures, no such messages or switches) | `home`, `origin`, `bgnd`, `cfg` would show them |
| `ahrs.set_takeoff_expected`/`set_touchdown_expected` (`AP_GroundEffect`) | never: `AP_GROUNDEFFECT_ENABLED 0` | `tkd` stays 0 |

The baro ground pressure also changes at 14.485 s, from inside the estimator (AP_Baro's field elevation from the EKF origin calls `ahrs.resetHeightDatum` and `update_calibration`). What the estimator reads from the vehicle besides these: AP_DAL's frame header (`AP::vehicle()->get_time_flying_ms()`, the armed flag, home, vehicle class, fly forward, takeoff/touchdown expected, trim, EKF type), AP_Baro's field elevation (armed flag), AP_InertialSensor's convergence time (armed flag), parameters (storage image), and the HAL: per consumed line the timer processes (the sensor stand-ins, which call the front ends' `_notify_new_*`, `accumulate_sample`, ...), the timer failsafe and the IO processes, and the IO processes after every `loop()`. Logging is compiled out (`HAL_LOGGING_ENABLED 0`). A replay applies the recorded state of a step to the estimator before the next step's tasks; the setter's task (table) says where in the step the call happened. In these flights no estimator task between a setter and the end of its step depends on the value set (after the disarm at 87.2 s `AP_Baro::update`, task 16, reads the armed flag, but only in its field-elevation branch, inactive by then). The estimator also writes to the vehicle (GCS text, AP_Notify flags, the baro's ground pressure parameter `set_and_save` into storage), which only the vehicle phase needs.

### Commands and results (2026-11-11)

```
python3 reference/build.py
for F in lockstep-flight lockstep-flight-noisy; do D=sim/out/$F
  build/reference/copter_ref --storage $D/storage_in.bin --est $D/est.txt < $D/inputs.txt > OUT; cmp OUT $D/outputs.txt; done
python3 reference/tools/est_compare.py sim/out/lockstep-flight/est.txt sim/out/lockstep-flight/est.txt
```

Both replays with `--est` reproduce `outputs.txt` byte for byte (`cmp` silent; 36,013 output lines, 36,013 est lines plus the task table; 52.7 MB each; 0.9 s instead of 0.2 s per replay). `reference/tools/est_compare.py A B [--from T] [--to T]` (T in µs, or seconds with a trailing `s`) matches steps by `t`, compares every comma-separated value as a string (bit pattern against bit pattern), and prints the steps compared, the values compared and equal, the first differing step and key with both values decoded, and the mismatch counts per key ordered by their first step; exit 0 iff all equal. A trace against itself: 36,013 steps, 5,037,573 values, all equal, exit 0. Against a copy with one bit of `c0.x[7]` flipped and `armed` changed at 50 s and `healthy` at 60 s: 3 different values, first difference at t = 50000000 key `armed`, other key `c0.x`, exit 1; with `--from 55s --to 70s` only `healthy`; with `--to 49997500` all equal, exit 0. The deterministic against the noisy flight shows the first difference in `bgnd` (the ground pressure calibrated at 1.76 s: 94503.65625 against 94503.6015625) and then the attitude from the first loop (2.2875 s).

## Not done in Phase 0

- No state digest in the output line (the plan's `--trace`): the output is the boundary only.
- QGroundControl was checked for connect, parameters and initial connect only, not the whole QGC-REQUIREMENTS checklist (mission upload from QGroundControl, arming, flight from QGroundControl); RC failsafe, battery failsafe, GPS glitch, two IMUs and the other modes were not flown.
- The Lean-side measurements of Phase 0 (FloatLib throughput, array-update cost) are not part of this work.
