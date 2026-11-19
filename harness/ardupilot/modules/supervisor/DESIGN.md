# supervisor: design of the proxy layer

The supervisor is ArduCopter's vehicle code (ArduCopter/*.cpp) and the libraries that serve it
(GCS_MAVLink, AP_Mission, AP_Arming, RC_Channel, AP_Scheduler, AP_Param, StorageManager,
AP_Vehicle, AP_Notify, AP_BattMonitor, SRV_Channel, AP_SerialManager, AP_Common, AP_Math, Filter),
compiled unmodified for the SITL board with the feature switches of `probe/features.txt`. Every
object of another stage that this code holds (AP_Vehicle's `ahrs`, `ins`, `gps`, `barometer`,
`compass` by value; Copter's `attitude_control`, `pos_control`, `wp_nav`, `loiter_nav`,
`circle_nav`, `motors` by pointer) exists in the process as a **shadow**: an object of the real
class, built from the real header, whose out-of-line methods are stand-ins and whose state is
written from the input record before the vehicle code runs.

Measurements behind this design: `measure/surface.tsv` (undefined symbols by owner),
`measure/access.tsv` (member accesses nm cannot see), `measure/proxy_surface.tsv` (every member
reached, with how it is reached and its role). `probe/probe.sh`, `probe/symbols.py`,
`probe/access_scan.py` (on the preprocessed sources), `gen/ast_extract.py` and
`gen/classify_surface.py` regenerate them.

## 1. A shadow per class

| Part of the class | In the supervisor | Source of the code |
|---|---|---|
| constructors | stand-in constructor with the real mem-initializer list and body (registers the singleton, sets parameter defaults) | text taken by `gen/` from the real .cpp |
| `var_info` | the real parameter table | text taken by `gen/` from the real .cpp |
| inline methods (header bodies) | run as written, on the shadow's state | the real header |
| out-of-line method, role *query* | stand-in returning the value from the shadow's state or the input record | `stand_ins/*.cpp`, hand-written per query |
| out-of-line method, role *command* | stand-in appending (method, arguments) to the tick's command log | generated |
| out-of-line method, role *own-task* (`update`, `init`, `periodic`, `wait_for_sample`, `rate_controller_run_dt`, `output`) | no-op: the stage runs it in its own step | generated |
| anything not classified | `abort()` naming the method: reaching it is a coverage hole, never a silent default | generated |

**Filling state.** Before each step the adapter writes the shadow fields that inline getters read
(e.g. `AC_PosControl::_pos_estimate_ned_m` for `get_pos_estimate_U_m`, `AP_Motors::_spool_state`
for `get_spool_state`, `AP_Motors::limit`, `AP_AHRS::roll/pitch/yaw`, `AP_AHRS::_home`). Private
fields are written through member pointers obtained by the explicit-instantiation rule (access is
not checked in an explicit instantiation's template arguments), the mechanism the mixer adapter
already uses for `AP_MotorsMatrix::_singleton`; `gen/` writes one accessor per field from
`classes.json`. Each shadow field is owned by exactly one side:

* *stage-owned*: written from the input record every tick (estimates, targets, limit flags, spool
  state); vehicle code that writes it is a coverage hole (aborts in debug builds via a write check).
* *supervisor-owned*: written only by vehicle code through inline setters (`set_interlock`,
  `set_spoolup_block`, `set_throttle_mix_min/max/man`, `set_vibe_comp`, `set_yaw_rate_tc`,
  `AC_WPNav::set_pause`, `AP_AHRS::lock_home`); persisted in the shadow and emitted as an output
  signal every tick (the brief's `interlock`, `spool_desired`, `clear_spoolup_block` are of this
  kind), so the stage applies the level, not an edge.

**What cannot be filled**: state behind references to further objects that have no signal (the
PID objects inside `AC_PosControl`/`AC_AttitudeControl`: `get_pid_info()` is answered from
`ac_`/`pc_` signals only for the fields GCS and crash_check read: I term, target, actual);
filter internals whose getters compute (`LowPassFilter` state); and anything whose meaning needs
the stage's code (`AC_WPNav::get_wp_acceleration_mss` computes from parameters: it is filled
with the guidance stage's parameters, so it is correct only if both modules have the same
parameter values, see 5).

## 2. Commands

A stand-in command records `(method, args)` into the tick's log. After the tick the adapter
writes the log into the output record as `cmd_<stage>_<method>` (bool) and
`cmd_<stage>_<method>_<arg>` (one field per scalar, vectors split `_x/_y/_z`, `Location` as
`_lat_e7/_lng_e7/_alt_cm/_frame`), the brief's form.

* **The same method twice in one tick.** Allowed only for methods declared *idempotent setters*
  (`*_set_max_speed_accel_m`, `*_set_correction_speed_accel_m`, `set_speed_*`,
  `set_desired_spool_state`, `set_throttle_out`): last call wins, which equals ArduCopter when no
  call in between reads the state they set. For any other method a second call with different
  arguments increments `sup_cmd_conflicts` (output, guaranteed 0 by the contract), so campaigns
  find the ticks where one record per method is not enough. Fallback if they are found: a
  per-stage ordered queue (`cmdq_<stage>_n`, `cmdq_<stage>_<i>_id`, `_<i>_a0..a7`), not built.
* **Order.** Each controller executes the set commands in one fixed order (documented by its
  module). The stand-in log keeps the actual order; if a tick's order is not a subsequence of the
  controller's fixed order, `sup_cmd_order_violations` increments (also guaranteed 0).
* **Commands that return a value** (`set_wp_destination_loc`, `set_spline_destination_*`,
  `set_origin`, `set_home`, `update_wpnav`, `calibrate_gyros`, `pre_arm_checks`, ...): the
  stand-in returns a predicted value computed from information the supervisor has (e.g. a
  destination is accepted iff the EKF origin is known and the location converts to NED, which is
  what `AC_WPNav::set_wp_destination_loc` checks without terrain); the stage outputs the actual
  result next tick (`wp_cmd_ok`, ...) and a monitor checks prediction = result. Each prediction is
  listed in stand_ins/README with the real code it mirrors.
* **In-out reference arguments** (`input_vel_accel_NE_m(vel&, ...)`,
  `input_pos_vel_accel_NE_m(pos&, vel&, ...)`, `input_vel_accel_D_m`, `input_pos_vel_accel_D_m`):
  the real method advances the caller's target by `update_vel_accel_xy` /
  `update_pos_vel_accel_xy` (AP_Math/control.cpp, compiled in the supervisor). The stand-in
  records the arguments as given, then makes the same AP_Math call on them with the shadow's
  `_dt_s`, so the mode's own copy of its target evolves as in ArduCopter.

## 3. Queries and how stale they are

Tick order `plant_sim → estimator → rate → mixer → supervisor → guidance → position → attitude`.
Estimator, rate and mixer outputs are of the same tick; guidance, position and attitude outputs
are one tick old.

* Same as ArduCopter: the estimator (`read_AHRS` runs before `update_flight_mode` in Copter's
  fast loop) and the mixer state (`motors_output_main` runs before it too).
* One tick older than ArduCopter, harmless: the mode reads a controller result that the controller
  produced in the previous tick in ArduCopter as well (`wp_nav->reached_wp_destination()`,
  `get_wp_distance_to_destination_m`, `pos_control->get_pos_desired_*` in the mission's
  `verify_*`, the land detector's `get_throttle`, `attitude_control->get_throttle_in`): the
  mission advances one tick (2.5 ms) later.
* One tick older, where behavior can change: reads right after a command in the same function.
  Found so far: `auto_takeoff_start` / `takeoff_run` (D_init_controller then
  `get_pos_desired_U_m`), mode `init()` functions that call `NE_init_controller()` and then read
  `get_stopping_point_NE_m` or `get_pos_target`, `ModeAuto::wp_start` (`wp_and_spline_init_m`
  then `get_wp_stopping_point_NED_m`), `ModeRTL` (`get_stopping_point_*` after the limit
  setters). In ArduCopter these see the post-init value; here they see last tick's. Decision to
  confirm: the stand-in of the init command applies the init's effect on the shadow fields that
  the reads use (e.g. after `D_init_controller`, `_pos_desired_ned_m.z = _pos_estimate_ned_m.z`),
  copied from the real init's assignments and listed per method; the stage's next output then
  overwrites the shadow with the real value. The alternative (accept the lag) changes takeoff
  altitude targets by one tick of climb.
* Controller-to-controller values (`get_thrust_vector()` into `input_thrust_vector_heading`) are
  not supervisor traffic: position outputs `thrust_vec_*`, attitude reads it.

## 4. The scheduler and the tick

`module_step` sets the clock (AP_HAL::micros/millis = `now_us`, frozen during the step as SITL's
simulated clock is), fills the shadows and the RC/GCS inputs, and calls `copter.loop()`
(AP_Vehicle::loop -> AP_Scheduler::loop, the real scheduler with Copter's real task table at
SCHED_LOOP_RATE = 400). With a frozen clock every due task fits its budget, so the task set per
tick is deterministic (as in SITL). The tasks that belong to other stages are not removed (the
table is real code); they run with their stage-side calls landing in own-task stand-ins:
`AP_InertialSensor::update` (no-op), `run_rate_controller_main` (its
`rate_controller_run_dt` is a no-op; the dt bookkeeping in it runs), `motors_output_main`
(runs: interlock, SRV_Channels and ESC-calibration logic are supervisor work; `motors->output()`
is a no-op), `read_AHRS` (`ahrs.update` is a no-op: the shadow was filled before the tick).

## 5. MAVLink across the boundary

A stand-in `AP_HAL::UARTDriver` serves SERIAL0 (the GCS port). Input fields `gcs_rx_len` (u32)
and `gcs_rx_w00..w63` (u32, four bytes each, little-endian); output fields `gcs_tx_len`,
`gcs_tx_w00..w63`. Capacity 256 bytes per tick each way = 102.4 kB/s at 400 Hz (QGroundControl's
steady traffic is a few kB/s; a full parameter download is ~40 kB). TX: the UART keeps a
4096-byte ring as ArduPilot's SITL UART does; `txspace()` reports its free space, so GCS_MAVLINK's
own flow control holds messages back when it is full (no loss); each step drains at most 256
bytes into the record. RX: the bytes of the record are appended to a 4096-byte ring; if it is full
the excess is dropped and counted in `gcs_rx_dropped` (the feeder outside should never send more
than the supervisor consumes: `update_receive` reads all available bytes each tick). The bridge
between the record and a UDP/TCP socket is outside the module (not built; no ports opened).

## 6. Parameters

The supervisor owns AP_Param (StorageManager on a RAM-backed `AP_HAL::Storage`, zeroed at init,
so every parameter starts at its var_info default) and the MAVLink parameter protocol; the
shadows carry the real var_info tables, so the ground station sees the whole ArduCopter list.
The parameter record of the module (`init`) sets: the supervisor's own parameters it uses
(FLTMODE*, ARMING_*, FS_*, PILOT_*, LAND_*, RTL_*, WP_*, MIS_*, BATT_*, RC*_ channel ranges) and
the other stages' parameters that supervisor code reads through inline getters (WPNAV_SPEED*,
WPNAV_ACCEL*, PSC_*_MAX, MOT_THST_HOVER, ATC_ANGLE_MAX ...), named as in the brief so the
composite feeds both modules the same value. In flight: a PARAM_SET of a supervisor parameter
takes effect (ArduCopter behavior); a PARAM_SET of another stage's parameter is refused (the
answer is a PARAM_VALUE with the unchanged value) because the other module's parameters are fixed
at its `init`. Decision to confirm: refuse, or add per-stage `prm_<stage>_idx/_val` command fields.

## 7. Boot

`module_init` builds the HAL stand-in (clock 0, RAM storage, harness UART, RC input from the
record, RC output recorded), resets the singletons, constructs `Copter` in zeroed storage (as
the static `copter` object is), sets the parameter record into AP_Param, and runs
`AP_Vehicle::setup()` (which calls `Copter::init_ardupilot`). Boot calls into other stages
(`gps.init`, `ins.init`, `barometer.calibrate`, `startup_INS_ground` ->
`ahrs.init/reset`, `ins.init(400)`, `motors->init`, `attitude_control->parameter_sanity_check`)
are own-task or local stand-ins; the other stages boot in their own `init`.

## 8. As built (scoping round)

* **Files.** `gen/run.sh` (called by `build.sh`) reads the shadow classes' declarations from
  clang's AST (`gen/ast_extract.py`) and writes `gen/out/shadow_<Class>.cpp` for 31 classes
  (`gen/gen_shadows.py`, SHADOWS): 24 real constructors and 16 real var_info tables copied as
  text from the real .cpp (estimator classes get empty tables), 13 real method bodies copied
  (COPY_REAL: functions of parameters or of filled state), 343 command stand-ins, 42 own-task
  no-ops, 414 query stand-ins that abort. Hand-written stand-ins (`stand_ins/*.cpp`, each with
  a header table of what it stands for) override the generated ones by name.
* **Discovery mode.** `SUP_LENIENT=1` makes an aborting query return its type's zero and count
  it (output `unanswered`, guaranteed 0): a tool to list the queries a scenario reaches, never
  evidence.
* **Feature switches** are a forced-include header written from `probe/features.txt` (as ~470
  `-D` flags they overflowed the 16 kB describe buffer of cpp/module_protocol.h).
* **A second `init`** re-executes the program (`execv` of itself, the parameter record in the
  environment); the new image boots in a static constructor of adapter.o (linked last, so it
  runs after `Copter copter` is constructed) and serves the session with a copy of
  module_protocol.h's loop. Every static and singleton is fresh, as at boot. Tested: three
  inits in one session.
* **Parameters** from the record are applied as parameter defaults through
  `hal.util->set_cmdline_parameters()`, which `AP_Param::load_all` calls on the SITL board
  (SITL's `--param` path).
* **Main.** Copter.cpp's `main` is renamed by ArduPilot's own hook `AP_MAIN` (flags.txt).
* **Link** with `-ld_classic` as waf does on darwin (the packed AP_FWVersion's unaligned
  pointers).

## 9. Findings

* STABILIZE at rest, disarmed, emits 7 commands every tick (rate_controller_target_reset,
  landed_gain_reduction(1), set_desired_spool_state(GROUND_IDLE), reset_yaw_target_and_rate,
  reset_rate_controller_I_terms, input_euler_angle_roll_pitch_euler_rate_yaw_rad(0,0,0),
  set_throttle_out(0,true,0)): "no commands at rest" is not ArduCopter's behavior; the
  controllers must accept these every tick.
* Order within a tick is not one fixed order per controller: GUIDED's takeoff calls
  `D_update_controller` and then `D_init_controller` in the same tick (tick 1201 of
  `dev/drive.py guided`), mode init calls the limit setters then the inits, the run functions
  call update then nothing. A controller that executes its commands in a fixed order must put
  init before update; the takeoff tick then differs from ArduCopter (the update ran on the
  pre-init state there). Needs the per-stage queue (2) or an agreed order with a monitor.
* `NE_is_active`/`D_is_active` ("updated in this or the previous scheduler tick") map exactly
  onto a previous-tick signal plus "commanded this tick".
* The estimator's telemetry senders (`AP_GPS::send_mavlink_gps_raw`, `send_mavlink_gps2_raw`)
  are classified as commands by the generator, so GPS_RAW_INT is never sent: they must become
  hand-written senders from `est_gps_*` signals.
* Random parameters reach code paths with unanswered queries (`AP_Baro::arming_checks`,
  `AP_GPS::pre_arm_checks`, `AP_InertialSensor::get_gyro_health_all`, `Compass::use_for_yaw`,
  `AC_WPNav::get_terrain_source`) and, in discovery mode with FS_THR_ENABLE outside its range,
  one segmentation fault not yet located.

## 10. Round 2 (decisions applied)

* **Commands as fields** (decision 1): `commands.txt` maps each stand-in call to the
  controllers' fields; `gen/gen_commands.py` writes `gen/Commands.lean` (58 targets, 212
  fields: `cmd_<stage>_<method>`, `_seq`, arguments) and the C++ that fills them. `_seq` is the
  call's place in the tick's whole log, from 1. A command not called keeps its last arguments
  (first values: AC_PosControl's constructor limits). Calls no field takes are counted in
  `cmd_unmapped`: rate_controller_target_reset (every tick), AP_AHRS::set_terrain_hgt_stable
  (50 Hz), AP_AHRS::set_home (boot, arming), output_min (arming), save_params_on_disarm
  (disarm). Inline setters (set_yaw_rate_tc, set_roll_pitch_rate_tc, set_throttle_mix_min/man,
  set_vibe_comp, set_pause/resume) are detected by a change of the shadow field and placed
  after every logged call.
* **Same-tick post-conditions** (decision 2): stubs_position.cpp (NE/D_init_controller: desired
  position and velocity from the estimate, the yaw target; is_active after an init or update),
  stubs_guidance.cpp (set_wp/spline_destination: origin, destination, reached and fast flags).
  The in-out arguments of input_*_m are advanced with the AP_Math call the real method makes.
* **Shadow state** filled from the stages' outputs: stubs_position.cpp, stubs_attitude.cpp,
  stubs_guidance.cpp, stubs_mixer.cpp, stubs_ahrs.cpp, stubs_sensors.cpp (each with its table).
* **Parameters** (decisions 3, 4): the estimator classes' real tables are served (753
  parameters); a PARAM_SET of any parameter inside a shadow object is refused by ArduPilot's
  @READONLY mechanism (stubs_params.cpp; 384 parameters): STATUSTEXT "Param write denied",
  PARAM_ERROR permission denied, PARAM_VALUE with the old value; counted in `param_set_refused`.
* **Strict mode** is now opt-in (`SUP_STRICT=1` aborts on an unanswered query); by default an
  unanswered query returns its type's zero and is counted in `unanswered` (guaranteed 0), so a
  campaign never stops on one.
* **Full stack**: ardupilot/harnesses/ap_full (plant_sim, truth_est, rate_c, mixer, supervisor, guidance,
  position, attitude); dev/fly.py flies it over `harness serve ap_full`; dev/udp_bridge.py
  relays it to UDP 127.0.0.1:14560 in real time; dev/gcs_client.py is the headless test client.

## 11. Round 3

* **Rebased** at 14:57 on h-apctl (Harness, cpp, every module but this one, harnesses, Main.lean,
  Top.lean; SNAPSHOT_h-apctl_time.txt). New command fields: cmd_attitude_rate_controller_
  target_reset, cmd_mixer_output_min / _update_throttle_hover / _set_thrust_boost (inline
  setter, change-detected), cmd_estimator_set_home / _reset_height_datum / _request_yaw_reset
  (NavEKF3::requestYawReset). Output `likely_flying` (AP_Vehicle::get_likely_flying) feeds the
  estimator; input `throttle_hover` comes from the mixer (the supervisor no longer outputs one).
  In the main project AP_AHRS::set_terrain_hgt_stable (baro_ground_effect.cpp) is mapped to
  the estimator's command cmd_estimator_set_terrain_hgt_stable (the real call there). Call
  still without a taker: with RC, AP_Motors::set_radio_passthrough (every tick).
* **Telemetry from signals**: GPS fix and velocity, barometer pressure and temperature from the
  simulator's samples (gps_*, baro_*); health, pre-arm verdict, hdop/vdop, vibration, clip
  count, innovations from new estimator outputs (ardupilot/modules/estimator in this copy: est_prearm_ok,
  est_ins_accel_healthy, est_ins_gyro_healthy, est_baro_healthy, est_gps_healthy,
  est_gps_hdop, est_gps_vdop, est_vibe_*, est_accel_clip_count, est_innov_ok, est_innov_vel_*,
  est_innov_pos_*). The compass shadow still has no instance (mag_* are read in but unused).
* **Poison trap**: SUP_POISON=1 (DESIGN.md: supervisor_shadow.h; gen/gen_shadows.py POISON).
* **Bridge**: dev/udp_bridge.py --gcs HOST:PORT (send to a listening ground station),
  ardupilot/fly_qgc.sh [PORT] in the main project (dev/fly_qgc.sh forwards to it;
  QGroundControl's default 14550; tested only with 14560).
* **What runs in this process that is controller code**: no control law. Copied real bodies
  (gen/ COPY_REAL) are parameter functions (lean_angle_max_rad, get_slew_yaw_max_rads,
  AC_Loiter::get_angle_max_rad, AC_PosControl::get_lean_angle_max_rad, pre_arm_checks,
  check_mot_pwm_params), functions of filled state (get_althold_lean_angle_max_rad,
  crosstrack_error_m), and AC_WPNav's Location-to-NED conversions and stopping point. The
  stand-ins replay the in-out argument updates of input_*_m with AP_Math's update_vel_accel(_xy)
  / update_pos_vel_accel(_xy) and apply the post-conditions of the inits and destination setters
  (a few assignments). AC_Loiter's and AC_Circle's control code is not run anywhere.

## 12. Round 4: the loiter stage

* AC_Loiter's calls are commands of the loiter stage (`ardupilot/modules/loiter`, commands.txt):
  set_speed_max_NE_ms, set_pilot_desired_acceleration_rad (clear_pilot_desired_acceleration is its
  inline call with 0, 0), soften_for_landing, init_target_m, init_target, update. `update` was an
  own-task no-op by its name; gen/gen_shadows.py now takes it out (`NOT_OWN_TASK`) and gives it a
  fixed command id (1000), so that every other command keeps its id and `cmd_log_hash` of the
  earlier cases is unchanged. The shadow's stage label is `loiter`.
* `AC_Loiter::get_angle_max_rad` is answered from the loiter stage's `lt_angle_max` of the
  previous tick (stand_ins/stubs_guidance.cpp; input `lt_angle_max`), so that LOIT_ANG_MAX is the
  loiter stage's parameter; it was a copied real body on the shadow's default parameters.
* `AC_PosControl::get_bearing_to_target_rad` (ModeLoiter::wp_bearing_deg, NAV_CONTROLLER_OUTPUT)
  is a copied real body (gen/ COPY_REAL) on the filled `_pos_target_ned_m` and `_pos_estimate_ned_m`.
* With RC in LOITER the one unmapped call per tick is AP_Motors::set_radio_passthrough, as in ALT_HOLD.
