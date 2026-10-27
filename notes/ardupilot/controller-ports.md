# ArduCopter waypoint navigator: component ports

Source studied: the clone at `ardupilot/` (HEAD 3d066385b6ac, commit date 2026-10-26). All paths below are relative to that root. Nothing was built or run; this is a static reading.

**What differs from the brief.**
- The parameters are now `WP_*` in metres. The old `WPNAV_*` names in cm were converted in 4.7 (AC_WPNav.cpp:115-163; group prefix `WP_` at ArduCopter/Parameters.cpp:370).
- SCurve now lives in `libraries/AP_Math/SCurve.{h,cpp}`, not in AC_WPNav.
- This tree adds two kinds of leg that upstream does not have. ARC_WAYPOINT gives an S-curve arc leg. LOITER_TURNS is flown as one S-curve arc leg over all the turns (`set_circle_destination_NED_m`), not through AC_Circle.
- The class that is actually built is `AC_WPNav_OA`, the avoidance subclass, whenever OA is compiled in (ArduCopter/system.cpp:490).

---

## 1. Component boundary

The component starts where ModeAuto hands a navigation mission item to `AC_WPNav`, and it ends where `AC_WPNav` writes a position, velocity and acceleration target into `AC_PosControl`.

**Per mission item.** `AP_Mission::update()` (libraries/AP_Mission/AP_Mission.cpp:310) runs inside `ModeAuto::run()` on every tick (ArduCopter/mode_auto.cpp:119). On every tick it calls `ModeAuto::verify_command`. When that returns true, it calls `ModeAuto::start_command` for the next navigation item. Item handlers and the navigator calls they make:

| Mission item | Handler (mode_auto.cpp) | Navigator calls |
|---|---|---|
| NAV_WAYPOINT, NAV_ARC_WAYPOINT | `do_nav_wp` (:1578) | `wp_start` (:465), which calls `AC_WPNav::wp_and_spline_init_m` only if the navigator is inactive, then `AC_WPNav::set_wp_destination_loc`. Then `set_next_wp` (:1623) calls `AC_WPNav::set_wp_destination_next_loc` or `set_spline_destination_next_loc`. |
| NAV_SPLINE_WAYPOINT | `do_spline_wp` (:1838) | `set_spline_destination_loc` |
| NAV_LOITER_UNLIM, NAV_LOITER_TIME | `do_loiter_unlimited` (:1726), `do_loiter_time` (:1789) | `wp_start` |
| NAV_LOITER_TURNS | `do_circle` (:1754), then `circle_movetoedge_start` (:545) and `circle_start` (:595) | `set_wp_destination_NED_m`, then `set_circle_destination_NED_m` |
| DO_CHANGE_SPEED | `do_change_speed` (:2017) | `set_speed_NE_ms`, `set_speed_up_ms`, `set_speed_down_ms` |

Completion is tested by `verify_nav_wp` (:2297), `verify_spline_wp` (:2362), `verify_loiter_time` (:2225) and `verify_circle` (:2326). All of them read `AC_WPNav::reached_wp_destination()`.

**Per tick.**
1. `ModeAuto::wp_run()` (:1134) calls `AC_WPNav::update_wpnav()` (AC_WPNav.cpp:713).
2. `update_wpnav()` calls `advance_wp_target_along_track(dt)` (:557).
3. That function advances the S-curve legs and calls `AC_PosControl::set_pos_vel_accel_NED_m` (:636).
4. `update_wpnav()` then calls `AC_PosControl::NE_update_controller()` itself (:741).
5. `wp_run` calls `D_update_controller()` afterwards (mode_auto.cpp:1150).

So, strictly, the per-tick call into the component also executes the horizontal position controller. For the contract, treat the call at step 3 as the output boundary.

**Tick rate.** `update_flight_mode` is a FAST_TASK (ArduCopter/Copter.cpp:136), so the whole chain runs once per main loop. The default loop rate is `SCHED_LOOP_RATE` = 400 Hz (libraries/AP_Scheduler/AP_Scheduler.cpp:44), clamped to 50-2000 Hz (:110-113). `dt` is the measured length of the last loop (ArduCopter/Attitude.cpp:14), not the nominal period.

---

## 2. Input ports

Frame conventions used throughout:
- "NED-origin" means metres, North-East-Down, as an offset from the EKF origin.
- "terrain-relative z" means the Down component is measured from the terrain surface, not from the origin.

### 2a. Written by the mission (planner side)

| Port | Dir | C++ source | Type | Units / frame | Writer | Rate | Limits enforced in code | Notes |
|---|---|---|---|---|---|---|---|---|
| `cmd_id` | in | `Mission_Command::id` (AP_Mission.h:432) | uint16_t | MAV_CMD enum | planner | per item | Unknown ids are skipped: verify returns true (mode_auto.cpp:1103-1108). | Selects the handler (mode_auto.cpp:765-901). |
| `dest` | in | `Mission_Command::content.location` (AP_Mission.h:426); `Location` fields lat/lng/alt (libraries/AP_Common/Location.h:18-20) | int32 lat, lng, alt plus frame bits | lat/lng in 1e-7 deg WGS-84. alt in cm, in one of four frames: above home, absolute, above origin, above terrain. `AC_WPNav::get_vector_NED_m` (AC_WPNav.cpp:1036-1066) converts it to NED-origin metres. z is above-origin, or terrain-relative when the frame is above terrain. | planner | per item | lat/lng range checked at upload (AP_Mission.cpp:1566-1570). lat=lng=0 means "use the default"; alt=0 means "use the default altitude" (mode_auto.cpp:1557-1572). | The default is the navigator's current destination if it was reached, else the vehicle position minus PosControl offsets (mode_auto.cpp:1581-1591). NE uses a flat-earth conversion from the origin (Location.cpp:269-278). |
| `next_dest` | in | location of the next nav item, from `AP_Mission::get_next_nav_cmd` (AP_Mission.h:643; called at mode_auto.cpp:1633) | `Location` | as `dest` | planner | per item (one item of lookahead) | Used only if the current item has p1 == 0 and the next item is WAYPOINT, LOITER_UNLIM, LOITER_TIME, PAYLOAD_PLACE, LAND, SPLINE or ARC (mode_auto.cpp:1627-1684). For LAND, alt is forced to 0, i.e. hold the current altitude (:1640-1642). | When accepted, this enables fast-waypoint behaviour (section 5i). |
| `next_cmd_id` | in | `next_cmd.id` (mode_auto.cpp:1638) | uint16_t | enum | planner | per item | Any other type means stop at `dest`. | |
| `delay_s` | in | `Mission_Command::p1` (AP_Mission.h:433) for WAYPOINT and SPLINE | uint16_t | s | planner | per item | none | Hold time after reaching the waypoint (mode_auto.cpp:1607, 2314). Any p1 > 0 disables lookahead (:1627). |
| `arc_angle` | in | `p1` and `location.loiter_ccw`, decoded by `get_arc_angle_rad` (AP_Mission.h:464-467) | float | rad, sign = turn direction (p1 is integer degrees) | planner | per item | An angle below 1 deg after wrapping is flown as a straight leg (SCurve.cpp:89). | Applies to the leg that ends at the ARC item (mode_auto.cpp:1675). |
| `loiter_time_s` | in | `p1` for LOITER_TIME (mode_auto.cpp:1798) | uint16_t | s | planner | per item | none | Timer starts once `reached` is true (:2228-2239). |
| `circle_radius`, `circle_turns`, `circle_dir` | in | `p1` high byte (radius, m; x10 if `type_specific_bits` bit 0), `get_loiter_turns` (p1 low byte, /256 if bit 1), `loiter_ccw` (mode_auto.cpp:1767-1780; AP_Mission.h:451-459) | uint16, float, bit | m, turns, CW/CCW | planner | per item | Radius is clamped by AC_Circle (mode_auto.cpp:553-554). Radius 0 means a yaw-only spin (:601-632). Orbit angle below 1 deg gives a zero-length leg (SCurve.cpp:136). | |
| `spd_type`, `spd_target` | in | `content.speed.speed_type` and `.target_ms` (AP_Mission.h:91-95; decoded at AP_Mission.cpp:1289-1293) | uint8, float | MAVLink SPEED_TYPE; m/s | planner | per DO item | Must be > 0 or the item is ignored (mode_auto.cpp:2019). Horizontal speed must be >= 0.01 (AC_WPNav.cpp:281). No upper bound. | Takes effect when the DO item is started, which is after the preceding nav item completes (AP_Mission.cpp:2157-2253). Also stored as an override that is re-applied on re-init (mode_auto.cpp:475-485). |
| `pause` | in | `ModeAuto::pause()`/`resume()`, which call `AC_WPNav::set_pause/set_resume` (mode_auto.cpp:2427-2445; AC_WPNav.h:86-89) | bool | — | GCS or script | event | Ignored if already reached (mode_auto.cpp:2432). | Ramps the progress rate to zero (AC_WPNav.cpp:596). |

### 2b. Parameters

AP_Param `@Range` values are ground-station metadata. AC_WPNav enforces only the clamps listed in the "Code-enforced" field.

| Port | C++ member (AC_WPNav.h) | Param | Type | Units | Default | `@Range` | Code-enforced | Notes |
|---|---|---|---|---|---|---|---|---|
| `p_spd` | `_wp_speed_ms` :379 | WP_SPD | AP_Float | m/s | 10.0 (AC_WPNav.cpp:8) | 0.10-20 | min 0.01, written back to the parameter at init (:220). Desired speed min 0.01 (:229). | Changing it in flight is picked up only if no explicit speed was given at init (:227, :716-722). |
| `p_radius` | `_wp_radius_m` :382 | WP_RADIUS_M | AP_Float | m | 2.0 | 0.05-10 | min 0.05, written back (:217) | Roles in section 5i. |
| `p_spd_up` | `_wp_speed_up_ms` :380 | WP_SPD_UP | AP_Float | m/s | 2.5 | 0.10-10 | none | Watched every tick (:724-727). |
| `p_spd_dn` | `_wp_speed_down_ms` :381 | WP_SPD_DN | AP_Float | m/s, positive | 1.5 | 0.10-10 | absolute value taken (AC_WPNav.h:124) | Watched every tick (:728-731). |
| `p_acc` | `_wp_accel_mss` :383 | WP_ACC | AP_Float | m/s² | 2.5 | 0.50-5 | if <= 0, 2.5 is used (AC_WPNav.h:140) | Along-track acceleration limit, and the ramp rate for pause. |
| `p_acc_z` | `_wp_accel_z_mss` :385 | WP_ACC_Z | AP_Float | m/s² | 1.0 | 0.50-5 | none | Section 5v: a value <= 0 disables every leg. |
| `p_acc_c` | `_wp_accel_c_mss` :384 | WP_ACC_CNR | AP_Float | m/s² | 0 | 0-5 | if <= 0, 2 x WP_ACC is used (AC_WPNav.h:144) | Corner-admission test and arc speed cap. |
| `p_jerk` | `_wp_jerk_msss` :386 | WP_JERK | AP_Float | m/s³ | 1.0 | 1-20 | if <= 0, set to WP_ACC at init (:238-240) | Also sets the progress-filter time constant WP_ACC/WP_JERK (:603-607). |
| `p_ter_margin` | `_terrain_margin_m` :387 | WP_TER_MARGIN | AP_Float | m | 10.0 | 0.1-100 | min 0.1 (AC_WPNav.h:61) | Vertical error at which progress slows (section 5iii). Applies even when not terrain-following. |
| `p_rfnd_use` | `_rangefinder_use` :425 | WP_RFND_USE | AP_Int8 | bool | 1 | 0/1 | — | Selects the rangefinder as the terrain source (:190). |
| `p_rate_rp` | AC_AttitudeControl `_ang_vel_{roll,pitch}_max_degs` | ATC_RATE_R_MAX, ATC_RATE_P_MAX | float | deg/s | 0 (meaning no limit) | 0-1080 | jerk cap = min(roll, pitch) x g, only if non-zero (AC_WPNav.cpp:1073-1078) | Read only at init. |
| `p_acc_rp` | AC_AttitudeControl `_accel_{roll,pitch}_max_degss` | ATC_ACC_R_MAX, ATC_ACC_P_MAX | float | deg/s² | 1100 (AC_AttitudeControl.h:22) | — | snap cap = min x g (:1085-1088) | Read only at init. |
| `p_input_tc` | AC_AttitudeControl `_input_tc` | ATC_INPUT_TC | float | s | 0.10 for Copter (AC_AttitudeControl.cpp:16) | 0-1 | floored at 0.1 inside the snap formula (:1082) | Read only at init. |
| `p_psc_jerk` | AC_PosControl `_shaping_jerk_ne_msss` | PSC_NE_JERK | float | m/s³ | 5.0 | 1-50 | — | Jerk for the pause/terrain speed ramp (:597-598). |
| `p_psc_kp` | AC_PosControl `_p_pos_ne_m` kP | PSC_NE_POS_P | float | 1/s | 1.0 for Copter (AC_PosControl.cpp:63) | — | — | Used in the lag-based slowing of progress (:589). |
| `p_loop` | AP_Scheduler `_loop_rate_hz` | SCHED_LOOP_RATE | int | Hz | 400 | — | clamped 50-2000 | Sets the tick rate. |

With the defaults (no rate limits, INPUT_TC 0.1, ACC_R_MAX 1100), the S-curve gets jerk 1 m/s³ and snap 7.85 m/s⁴ (= 0.5 x pi/(2 x 0.1)). The jerk ramp time is then tj = 0.2 s (SCurve.cpp:964). This is my own arithmetic.

### 2c. Environment and state inputs

| Port | Dir | C++ source | Type | Units / frame | Writer | Rate | Limits / validation | Notes |
|---|---|---|---|---|---|---|---|---|
| `pos_est` | in | `AC_PosControl::get_pos_estimate_NED_m()` (AC_PosControl.h:313), filled by `update_estimates` (AC_PosControl.cpp:1446-1465) | Vector3p (double when HAL_WITH_POSTYPE_DOUBLE) | m, NED-origin | EKF/AHRS, via `read_inertia` (ArduCopter/inertia.cpp:7) | per tick | None in the navigator. If AHRS has no horizontal position, the horizontal estimate is left at zero (AC_PosControl.cpp:1448-1455). | Used for the reached test with offsets removed (AC_WPNav.cpp:575-576), and for distance and bearing without offset removal (:691, :707). |
| `vel_est` | in | `get_vel_estimate_NED_ms()` (h:377) | Vector3f | m/s NED | EKF/AHRS | per tick | none | Progress slowing (:587). |
| `pos_err` | in | `get_pos_error_NED_m()` (h:361) | Vector3f | m NED; the PosControl P-loop error from the previous tick | PosControl | per tick | none | Progress slowing (:586). |
| `vel_des_fb` | in | `get_vel_desired_NED_ms()` and `get_vel_offset_D_ms()` (h:397, :500) | Vector3f, float | m/s NED | the navigator's own last output, after PosControl changes it | per tick | none | Sets the progress direction (:579-590), and seeds the spline-to-S-curve speed (:399-401). |
| `pos_ofs` | in | `get_pos_offset_NED_m()` (h:485) | Vector3p | m NED | PosControl offset users (outside) | per tick | none | Removed from `pos_est` before the reached test. |
| `lim_psc` | in | `NE_get_max_speed_ms`, `get_max_speed_up_ms`, `get_max_speed_down_ms` (h:112, :227, :230) | float | m/s | Written by the navigator itself, and also by other ModeAuto submodes (mode_auto.cpp:508, :701, :1221, :1830) | read when a leg is built or a speed changes | — | The S-curve takes its speed limits from PosControl, not from WP_SPD directly (AC_WPNav.cpp:419-422). |
| `terr_rf` | in | `set_rangefinder_terrain_U_m(use, healthy, terrain_u_m)` (AC_WPNav.h:30) | bool, bool, float | m, Up, terrain height relative to the EKF origin | rangefinder, via `sensors.cpp:63` (FAST_TASK at Copter.cpp:142) | per tick | Must be healthy, otherwise terrain is treated as unavailable (AC_WPNav.cpp:792-797). | |
| `terr_db` | in | `AP_Terrain::height_above_terrain` (AC_WPNav.cpp:804) | float | m above terrain at the vehicle, converted to terrain height Up relative to the origin (:806) | terrain database | per tick | A lookup failure returns false. | Used only if the rangefinder is not selected (:190-197). |
| `dt` | in | `_pos_control.get_dt_s()` (AC_PosControl.h:53; set at Attitude.cpp:14) | float | s | scheduler clock | per tick | none in the navigator | Measured, not nominal. |
| `now_ms` | in | `AP_HAL::millis()` (AC_WPNav.cpp:744, :754) | uint32 | ms | clock | per tick | — | `is_active()` means an update happened within the last 200 ms. |
| `ekf_origin` | in | `AP::ahrs().get_origin` (Location.cpp:272; AC_WPNav.cpp:361) | Location | WGS-84 | EKF | as needed | No origin means the destination conversion fails. | ModeAuto does not start the mission until an origin exists (mode_auto.cpp:95-101). |
| `pos_ok` | — | not read by the navigator | — | — | — | — | — | `copter.position_ok()` (system.cpp:215) is checked by ModeAuto on entry, by `loiter_start` (mode_auto.cpp:377), and by the EKF failsafe. None of these are inside the component. |
| `att_lims` | in | `get_ang_vel_*_max_rads`, `get_accel_*_max_radss`, `get_input_tc` (AC_AttitudeControl.h:91-139) | float | rad/s, rad/s², s | attitude controller parameters | read at init only (AC_WPNav.cpp:241) | see 2b | |

---

## 3. Output ports

| Port | Dir | C++ source | Type | Units / frame | Reader | Rate | Limits / guarantees in code | Notes |
|---|---|---|---|---|---|---|---|---|
| `pos_tgt` | out | `set_pos_vel_accel_NED_m(target_pos_ned_m, …)` (AC_WPNav.cpp:636; AC_PosControl.cpp:1183-1188) | Vector3p | m, NED-origin. z is terrain-relative when `terrain_alt` is true; PosControl adds the terrain offset (AC_PosControl.cpp:1101). PosControl offsets are not included; they are added later (:723, :874). | AC_PosControl | per tick, except ticks where terrain lookup fails | Lies on the leg's segment or arc, or on the blended corner (section 5ii). | |
| `vel_tgt` | out | same call | Vector3f | m/s NED | AC_PosControl (feed-forward); AutoYaw also reads it (ArduCopter/autoyaw.cpp:287) | per tick | Equals the path velocity x `vel_dt_scalar` (:631). | Not multiplied by `_track_dt_scalar`, so it is not the exact time derivative of `pos_tgt` (section 5vi). |
| `acc_tgt` | out | same call | Vector3f | m/s² NED | AC_PosControl | per tick | Equals the path acceleration x `vel_dt_scalar`², plus an along-track term `_offset_accel_mss` x \|v_path\| / v_des (:625-633). | Spline legs contribute no path acceleration (:611, :617-621). |
| `terr_tgt` | out | `set_pos_terrain_target_D_m(terr_offset_d_m)` (:569) | float | m, Down, terrain relative to the origin; 0 when not terrain-following | AC_PosControl | per tick | — | |
| `terr_reseed` | out | `init_pos_terrain_D_m` (:830, :834, :945, :949) | float | m Down | AC_PosControl | event: change of altitude frame | Shifts PosControl's desired z so the absolute target is unchanged (AC_PosControl.cpp:1243-1248). | |
| `psc_lims` | out | `NE_set_max_speed_accel_m`, `NE_set_correction_speed_accel_m`, `D_set_max_speed_accel_m`, `D_set_correction_speed_accel_m` (:232-235, :289-290, :302, :313) | float | m/s, m/s² | AC_PosControl | init and speed changes | — | The same state is read back as `lim_psc`. |
| `psc_reinit` | out | `D_init_controller_stopping_point`, `NE_init_controller_stopping_point` (:223-224) | call | — | AC_PosControl | on (re)init | Sets PosControl's desired position to its stopping point and its desired velocity and acceleration to zero (AC_PosControl.cpp:502-510, :868-877). | |
| `reached` | out | `reached_wp_destination()` (AC_WPNav.h:256). The OA subclass also requires OA to be inactive (AC_WPNav_OA.cpp:99-103). | bool | — | `verify_nav_wp`, `verify_spline_wp`, `verify_loiter_time`, `verify_circle`, `do_nav_wp` default (mode_auto.cpp:1586) | per tick | Once true, stays true until the next `set_*_destination`. | Section 5i. |
| `reached_ne` | out | `reached_wp_destination_NE()` (AC_WPNav.h:260-262) | bool | horizontal distance < WP_RADIUS_M | `loiter_to_alt_run` (mode_auto.cpp:1212) | on call | — | Computed live; not latched. |
| `dist` | out | `get_wp_distance_to_destination_m()` (AC_WPNav.cpp:688-692); OA override (AC_WPNav_OA.cpp:65-74) | float | m, horizontal, from `pos_est` to the destination | GCS (GCS_MAVLink_Copter.cpp:191), Copter.cpp:920 | on call | ≥ 0 | |
| `bearing` | out | `get_wp_bearing_to_destination_rad()` (:704-708) | float | rad in [0, 2pi), clockwise from North (libraries/AP_Math/location.cpp:27-30) | GCS (via `wp_bearing_deg`, mode_auto.cpp:956) | on call | — | A centidegree version also exists (:696). |
| `dest_out` | out | `get_wp_destination_NED_m()`, `get_wp_destination_NEU_cm()`, `get_wp_destination_loc()` (AC_WPNav.h:148-152; cpp:358-368) | Vector3p, Vector3f, Location | m NED-origin, or cm NEU; z is terrain-relative if `terrain_alt`; Location in the above-origin or above-terrain frame | ModeAuto default location (mode_auto.cpp:1587), logging, GCS | on call | — | `get_oa_wp_destination` returns the OA intermediate point (AC_WPNav_OA.cpp:16-26). |
| `origin_out` | out | `get_wp_origin_NED_m()` / `_NEU_cm()` (AC_WPNav.h:156-160) | Vector3p | as `dest_out` | logging, other modes | on call | — | |
| `terrain_alt` | out | `origin_and_destination_are_terrain_alt()` (AC_WPNav.h:164) | bool | — | other modes | on call | — | |
| `spd_defaults` | out | `get_default_speed_NE_ms`, `_up_ms`, `_down_ms`, `get_wp_acceleration_mss`, `get_accel_D_mss`, `get_corner_acceleration_mss`, `get_wp_radius_m`, `get_terrain_margin_m` (AC_WPNav.h:104-144, :61, :266) | float | m/s, m/s², m | ModeAuto takeoff, land and loiter-to-alt; other modes | on call | Same fallbacks as in 2b. | These are parameter values. The current leg speed `_wp_desired_speed_ne_ms` has no public getter; it is only visible through `lim_psc`. |
| `stop_pt` | out | `get_wp_stopping_point_NED_m()` (:546-552) | Vector3p | m NED-origin | `loiter_start` (mode_auto.cpp:383) | on call | — | Delegates to PosControl. |
| `active` | out | `is_active()` (:751-755) | bool | — | `wp_start` (mode_auto.cpp:468), `do_nav_wp` | on call | — | |
| `paused_out` | out | `paused()` (AC_WPNav.h:92) | bool | — | ModeAuto | on call | — | |
| `circle_angle` | out | `get_circle_angle_covered_rad()` (AC_WPNav.h:221) | float | rad, unsigned, unwrapped | `verify_circle` (mode_auto.cpp:2349) | on call | 0 unless on an orbit leg | |
| `upd_ok` | out | return value of `update_wpnav()` (:713-747) | bool | false = terrain unavailable this tick | `failsafe_terrain_set_status` (mode_auto.cpp:1146; events.cpp:261) | per tick | — | 5 s of failures triggers the terrain failsafe (events.cpp:242-258; config.h:98). |
| `set_ok` | out | return values of `set_wp_destination_loc`, `_next_loc`, `set_spline_*`, `set_circle_destination_NED_m` | bool | false = location conversion or terrain failure | ModeAuto, which calls `failsafe_terrain_on_event` immediately (mode_auto.cpp:1597, :1613) | per item | — | |
| `terr_src`, `terr_u` | out | `get_terrain_source()`, `get_terrain_U_m()` (cpp:186-205, :784-815) | enum, float | m Up relative to origin | failsafe messages, takeoff, RTL | on call | — | |
| pass-through | out | `get_roll_rad`, `get_pitch_rad`, `get_yaw_rad`, `get_thrust_vector`, `crosstrack_error_m` (AC_WPNav.h:318-356) | float, Vector3f | rad, m | ModeAuto (`crosstrack_error_m`, mode.h:642) | on call | — | PosControl values relayed by the navigator; not produced by it. |

**Fast-waypoint and leg-complete state are not exported.** The fast-waypoint bit and the S-curve's finished state are protected members. Nothing in ArduCopter reads them; the only completion signal ModeAuto sees is `reached`.

---

## 4. Internal state

| Name | Type | Source | Meaning |
|---|---|---|---|
| `_scurve_prev_leg`, `_scurve_this_leg`, `_scurve_next_leg` | SCurve | AC_WPNav.h:396-398 | Jerk-limited profiles for the leg being left (still evaluated during a corner), the current leg, and the preloaded next leg. Each holds 23 time segments (SCurve.h:236-251), its own elapsed time `time`, and its own limits. |
| `_spline_this_leg`, `_spline_next_leg` | SplineCurve | AC_WPNav.h:403-404 | Spline legs, for NAV_SPLINE_WAYPOINT. |
| `_origin_ned_m`, `_destination_ned_m`, `_next_destination_ned_m` | Vector3p | AC_WPNav.h:414-416 | m, NED-origin; z is terrain-relative when `_is_terrain_alt`. |
| `_is_terrain_alt` | bool | :423 | Altitude frame of the origin and destination. |
| status bits `reached_destination`, `fast_waypoint` | 1-bit fields | :363-367 | Reached indicator; "will not stop at this destination". |
| `_this_leg_is_spline`, `_next_leg_is_spline`, `_this_leg_is_circle` | bool | :407-409 | Kind of leg. |
| `_wp_desired_speed_ne_ms` | float | :413 | Current horizontal speed target, m/s. |
| `_track_dt_scalar` | float in [0, 1] | :417 | Filtered progress rate, reduced when the vehicle lags. |
| `_offset_vel_ms`, `_offset_accel_mss` | float | :418-419 | Jerk-shaped speed ramp, used for pause and terrain slowing. |
| `_paused` | bool | :420 | |
| `_wp_last_update_ms` | uint32 | :412 | Timestamp for `is_active()`. |
| `_check_wp_speed_change`, `_last_wp_speed_*` | bool, float | :390-393 | Detects parameter changes in flight. |
| `_scurve_jerk_max_msss`, `_scurve_snap_max_mssss` | float | :399-400 | Derived jerk and snap limits. |
| ModeAuto `loiter_time`, `loiter_time_max`, `desired_speed_override_ms` | uint32, uint16, struct of floats | ArduCopter/mode.h:750-751, :805-810 | Hold timer; stored overrides from DO_CHANGE_SPEED. |
| OA backups `_origin_oabak_ned_m` etc., `_oa_state` | Vector3p, enum | AC_WPNav_OA.h:60-66 | Out of scope. |

---

## 5. Behavioural facts

### (i) Switching from one leg to the next

**How fast-waypoint is set.**
- `set_wp_destination_next_NED_m` preloads `_scurve_next_leg` from the current destination to the next one, and sets fast-waypoint to true (AC_WPNav.cpp:487-514).
- It does nothing, while still returning true, if the next point uses a different altitude frame (:490-492). In that case the vehicle stops at the waypoint.
- `set_wp_destination_NED_m` clears fast-waypoint whenever a new destination is set (:433).
- In Auto, the preload is requested only by `set_next_wp`, under the conditions listed for `next_dest` in 2a. Any p1 delay or an unsupported next item means the vehicle stops (mode_auto.cpp:1627-1684).

**Inside the S-curve on each tick** (`SCurve::advance_target_along_track`, SCurve.cpp:570-607):
1. The target starts at the leg origin. The previous leg's remaining motion, measured relative to its own end point, is added (:572). Then this leg's motion from its origin is added (:573).
2. If fast-waypoint is on and the next leg has not started, three timing conditions are checked (:578-582): this leg has entered its deceleration phase; its remaining time is no more than the next leg's acceleration-phase duration; and the next leg's time is still zero.
3. If those hold, the code predicts the combined target at the turn midpoint, i.e. half the remaining time (:585-588). It starts the next leg only if, at that predicted midpoint, all four of these hold (:591-597):
   - the target is within WP_RADIUS_M (3-D distance) of the waypoint;
   - the speed is below the smaller of the two legs' maximum speeds;
   - the horizontal acceleration is below the corner limit (WP_ACC_CNR, or 2 x WP_ACC);
   - the vertical acceleration is below the smaller WP_ACC_Z.
4. If the test fails, it is repeated on later ticks while the timing conditions still hold.
5. Once the next leg has started, it is advanced on every tick and added in. This leg reports finished when the next leg's elapsed time reaches this leg's remaining time, i.e. at the turn midpoint (:598-603).

**Reached rule** (AC_WPNav.cpp:639-652):
- Fast waypoint: `reached` becomes true as soon as the S-curve reports finished. The vehicle's position is not checked.
- Not fast: `reached` also requires the 3-D distance from the offset-corrected position estimate to the destination to be ≤ WP_RADIUS_M (:646-647). The S-curve finishes only once its target has stopped at the destination.

**Handover.**
- On the next tick, `AP_Mission::update` (AP_Mission.cpp:336-347) sees `verify_nav_wp` return true. That needs `reached`, and a delay of 0 s (mode_auto.cpp:2297-2323). It then starts the next item, and `set_wp_destination_NED_m` promotes the legs (AC_WPNav.cpp:404, :414-416).
- The promotion copies the current leg into the previous-leg slot and the preloaded leg into the current slot. Elapsed times are kept, so the blend carries on. A new leg is built from scratch only if a spline is involved or the preloaded leg is already finished (:414-427).

**What WP_RADIUS_M does.** It has three roles:
1. the corner-admission test (SCurve.cpp:591);
2. the acceptance sphere for a stop-at waypoint (AC_WPNav.cpp:647);
3. the horizontal test in `reached_wp_destination_NE` (AC_WPNav.h:261).

It is never used to declare a fast waypoint complete. The S-curve's own timing decides when the corner starts (the deceleration-phase and acceleration-phase overlap above) and when the leg is complete (the midpoint).

### (ii) How far the target can deviate from the polyline at a corner

**What the code checks.** Only one quantity: the 3-D distance from the blended target, at the predicted turn midpoint, to the waypoint must be below WP_RADIUS_M (SCurve.cpp:591). There is no test on the rest of the blend. The S-curve blend is the only thing that cuts corners; WP_RADIUS_M only admits a blend or rejects it.

**Bound for the whole blend (my derivation, not stated in the code).** For straight legs, the blended target is W − r(t)·u1 + s(t)·u2, where:
- W is the waypoint;
- u1 and u2 are the unit directions of the two legs;
- r is the distance remaining on leg 1 and never increases;
- s is the distance covered on leg 2 and never decreases. Segment positions are checked to be non-decreasing (SCurve.cpp:1231-1233), and the position output is clamped at zero or above (:842).

Let φ be the turn angle.
- Before the midpoint, the distance to the polyline is at most s·sin φ ≤ s_mid·sin φ.
- After the midpoint, it is at most r·sin φ ≤ r_mid·sin φ.
- Since \|−r_mid·u1 + s_mid·u2\|² ≥ max(r_mid, s_mid)²·sin²φ, the midpoint test gives max(r_mid, s_mid)·sin φ < WP_RADIUS_M.

So the target stays within WP_RADIUS_M of the polyline for the whole corner, provided all of the following hold:
- both legs are straight, not arcs;
- both legs are long enough that the perpendicular foot stays on the segments;
- no speed change happens during the blend.

The time scaling (`_track_dt_scalar` x `vel_dt_scalar`) does not change the geometry, because the same scaled dt is applied to all three legs in the same call (AC_WPNav.cpp:616). The predicted midpoint differs from the realised one by about half a tick, because the next leg is advanced by dt on the tick it is admitted (SCurve.cpp:596).

If admission never succeeds, the current leg slows to zero at W and there is no corner cutting.

Arc legs follow their arc. Their speed is capped at sqrt(corner accel x radius) (SCurve.cpp:197-201).

### (iii) Limits the S-curve enforces

Each leg is a scalar profile along the track, projected onto the leg's line or arc (SCurve.cpp:668-719).

**Maximum speed.** `kinematic_limit` (libraries/AP_Math/control.cpp:756) of the leg direction, with:
- horizontal limit = PosControl NE maximum speed (which tracks WP_SPD, or the DO_CHANGE_SPEED value);
- climb limit = PosControl up maximum;
- descent limit = PosControl down maximum.

It is the largest along-track speed whose horizontal component is within the horizontal limit and whose vertical component is within the climb or descent limit (SCurve.cpp:210). On arcs the horizontal limit is first reduced to sqrt(accel_c·R) (:197-201).

**Maximum acceleration.** `kinematic_limit` of WP_ACC (horizontal) and WP_ACC_Z (vertical) (:211). `calculate_path` keeps the constant-acceleration level at or below this (:965-967).

**Jerk.** At most `_scurve_jerk_max_msss`, i.e. min(WP_JERK, ATC rate limits x g) (AC_WPNav.cpp:1073-1078). It has a raised-cosine shape (SCurve.cpp:864-869).

**Snap.** At most `_scurve_snap_max_mssss` (AC_WPNav.cpp:1082-1091). The raised cosine's ramp time tj = Jm·pi/(2·Sm) (SCurve.cpp:964) gives a peak snap of exactly Sm.

**Arcs.** The centripetal term v²/R is added on top of the tangential acceleration (SCurve.cpp:709). The vector sum of the two is not limited jointly.

**Short legs.** The acceleration and deceleration halves are each planned over half the leg length (SCurve.cpp:907, :535, :463). For a short leg:
- the acceleration level is capped by (L − 4·V0·tj)/(4·tj²) (:967);
- from rest, tj is cut to the smallest of (L·pi/(8·Sm))^¼, (Vm·pi/(4·Sm))^⅓ and sqrt(Am·pi/(2·Sm)), and jerk and acceleration are reduced to match (:972-979);
- the cruise segment is set to max(0, …), so it is zero (:921).

The result is a symmetric accelerate-then-decelerate profile whose peak speed is below the limit. The leg still ends exactly at the destination with zero speed (:930).

When a leg is entered at a speed (set_origin_speed_max) and its acceleration cannot fit in half the length, the acceleration block is shifted earlier (:474-480).

**After the S-curve, before the outputs.** The output velocity is scaled by `vel_dt_scalar`. This is `_offset_vel_ms` divided by the desired speed, where `_offset_vel_ms` is ramped toward the desired speed x `offset_d_scalar`, or toward 0 when paused. The ramp is limited by ±WP_ACC and PSC_NE_JERK (AC_WPNav.cpp:593-600).

`offset_d_scalar` is `terrain_scaler_D_m` (AC_PosControl.cpp:433-440). It falls from 1 to 0.01 as the vertical tracking error grows from WP_TER_MARGIN/2 to WP_TER_MARGIN. Large vertical error therefore slows horizontal progress, even when not terrain-following.

`_track_dt_scalar` slows the progress clock, but not the velocity output, when the vehicle lags. It is 0.05 + (along-track speed − kP x along-track error)/\|v_target\|, clamped to [0, 1] and then low-pass filtered (AC_WPNav.cpp:583-607).

Output acceleration has no overall cap. It is the path acceleration x scalar² plus an along-track term bounded by about WP_ACC x \|v_path\|/v_des (:625-633).

**Spline legs.** Speed is limited by the PosControl maxima, and its change per tick by accel x dt (libraries/AP_Math/SplineCurve.cpp:120). They output no acceleration target and have no jerk limit.

### (iv) A new destination set in the middle of a leg

`set_wp_destination_NED_m`, `set_spline_destination_NED_m` and `set_circle_destination_NED_m` all re-initialise the navigator if it is inactive or the current destination has not been reached (AC_WPNav.cpp:386-388, :445-447, :906-908). Re-initialisation means:
- `wp_and_spline_init_m` sets both origin and destination to PosControl's stopping point. The stopping point is the current estimate plus a stopping distance along the current velocity (AC_PosControl.cpp:1382-1410).
- All three legs are cleared (AC_WPNav.cpp:243-245).
- PosControl is re-initialised with desired velocity and acceleration at zero (:223-224).
- The new leg then starts from that point at zero speed.
- Any preloaded next leg and the fast-waypoint state are discarded.

In Auto this happens when the mission is edited and the current item restarts (mode_auto.cpp:107-116), when a GCS sets the current item, and through OA.

`set_wp_destination_next_NED_m` has no guard against replacing a next leg that has already started blending. It rebuilds the leg with time 0 (AC_WPNav.cpp:495-498). In Auto it is called only straight after a new destination, when the next leg has not started.

### (v) Input validation and failure behaviour

**Terrain or origin unavailable when a destination is set.** `get_vector_NED_m` (:1036-1066), `convert_origin_to_alt_frame` (:820-838) and the spline frame change (:937-939) all return false. ModeAuto then calls `failsafe_terrain_on_event` straight away (mode_auto.cpp:1597, :1613, :1848-1862), which leads to RTL or land, or disarm if landed (events.cpp:281-305). A missing EKF origin goes down the same path and is reported as a terrain failure.

**Terrain unavailable during a tick.** `advance_wp_target_along_track` returns before advancing any leg and before writing targets (AC_WPNav.cpp:561-563). PosControl keeps the last desired position, velocity and acceleration. `update_wpnav` still runs NE_update_controller and returns false (:735-741). After 5 s of continuous failures (FS_TERRAIN_TIMEOUT_MS, config.h:98) the terrain failsafe fires (events.cpp:242-258).

**Rangefinder unhealthy.** Treated as terrain unavailable (AC_WPNav.cpp:792-797).

**Zero-length leg** (origin equals destination). `calculate_track` leaves a one-segment leg (SCurve.cpp:79-84). It reports finished at once (:610-613, :722-727) and outputs zero velocity at the origin.

**Invalid profile.** This covers non-positive or non-finite limits, a solver output that is not finite or is negative, or a segment table that fails `valid()`. The code raises INTERNAL_ERROR and calls `init()`, which leaves a zero-length leg (SCurve.cpp:215-222, :227-234, :951-957, :1016-1074, :1211-1245).

Consequence of that zero-length leg (my reading):
- The target holds at the leg origin while `_destination_ned_m` keeps the real destination.
- A fast waypoint completes at once.
- A stop-at waypoint never reaches unless the vehicle is already within WP_RADIUS_M, so the mission stalls with the vehicle hovering at the origin.

**Parameter values that disable every leg** (my reading). `kinematic_limit` returns 0 if any limit is ≤ 0 (control.cpp:759-761). So WP_ACC_Z ≤ 0, a zero climb or descent limit, or a zero NE speed makes every leg invalid as described above.

**Clamps that are applied.**
- WP_RADIUS_M ≥ 0.05 and WP_SPD ≥ 0.01, both written back to the parameter (AC_WPNav.cpp:217, :220).
- Desired speed ≥ 0.01 (:229).
- Fallbacks for WP_ACC, WP_ACC_CNR and WP_JERK (AC_WPNav.h:140, :144; cpp:238-240).
- WP_TER_MARGIN ≥ 0.1 (h:61).
- DO_CHANGE_SPEED must be > 0 (mode_auto.cpp:2019), and horizontal speed ≥ 0.01 (AC_WPNav.cpp:281). A NaN fails both comparisons and is ignored.

**Not checked anywhere in the component.**
- No maximum leg length or maximum distance to a waypoint.
- No upper limit on any speed.
- No NaN check on a NED destination given directly to `set_wp_destination_NED_m`.
- SCurve stores leg geometry and positions as float (`seg_delta`, `end_pos`; SCurve.h:249-254), while origins are `postype_t`.

**Arcs and frames.**
- An arc angle below 1 deg means a straight leg (SCurve.cpp:89).
- An orbit with radius 0 or angle below 1 deg means a zero-length leg (:136-139).
- A change of altitude frame between consecutive waypoints means the vehicle stops at the waypoint (AC_WPNav.cpp:490-492).

**Mission end.** `exit_mission` calls `loiter_start`. That sets the stopping point as the destination, or switches to LAND if the position is not OK (mode_auto.cpp:904-918, :374-396).

### (vi) Which outputs are continuous across leg changes

**Continuous.**
- **Fast-waypoint promotion.** `pos_tgt`, `vel_tgt` and `acc_tgt` are continuous. The previous leg's remaining motion and the current leg's motion are summed both before and after the promotion, with the same times (AC_WPNav.cpp:404, :414-416; SCurve.cpp:572-573). Within a leg the profile has bounded jerk and snap, so position is continuous up to acceleration.
- **Fast waypoint whose corner was never admitted.** Continuous. The old leg ends at rest at W and the new leg starts from rest.
- **Stop-at waypoint.** Continuous for the same reason.
- **Altitude-frame change.** The absolute z target stays continuous because PosControl's desired z is shifted by the change in terrain offset (AC_PosControl.cpp:1243-1248). This only happens at a waypoint where the vehicle stops.
- **Speed change during a leg.** `SCurve::set_speed_max` re-plans from the current time (SCurve.cpp:238-440), and `_offset_vel_ms` is rescaled so `vel_dt_scalar` does not jump (AC_WPNav.cpp:283). A speed change has no effect on a leg already decelerating (SCurve.cpp:269-271). Continuity of the re-planned branches was not checked numerically.
- **Pause and resume.** Speed is ramped with jerk limiting.
- **Terrain-failure tick.** No new target is written, and the S-curve clocks stop. When data returns, the target resumes from the same point.

**Not continuous.**
- **Mid-leg re-initialisation.** `pos_tgt` jumps to the stopping point, and `vel_tgt` and `acc_tgt` jump to zero (section 5iv).
- **Spline to S-curve.** The S-curve is seeded with the current speed magnitude (AC_WPNav.cpp:397-401). Direction and acceleration may jump, because spline legs output zero acceleration.

**Holds on every tick: velocity is not the derivative of position.** Because `vel_tgt` omits `_track_dt_scalar`, `vel_tgt` equals d(`pos_tgt`)/dt only when `_track_dt_scalar` = 1.

---

## 6. Object avoidance and fence (out of scope; for reference)

**Object avoidance.** `AC_WPNav_OA` (AC_WPNav_OA.cpp:107-306) wraps `update_wpnav`.
- It reads `AP_OAPathPlanner::mission_avoidance` with:
  - the vehicle Location;
  - the backed-up origin, destination and next destination as Locations;
  - the `OA_OPTION_FAST_WAYPOINTS` option.
- It writes:
  - intermediate destinations through `set_wp_destination_loc` and `set_wp_destination_next_loc`;
  - `force_stop_at_next_wp()` (AC_WPNav.cpp:761-779), when the path to the next waypoint is blocked;
  - for BendyRuler, direct position targets via `AC_PosControl::input_pos_NED_m(…, terrain, 10.0)`, which bypasses the S-curve.
- It replaces `reached`, `dist` and `bearing` so that they refer to the original destination (AC_WPNav_OA.cpp:65-103).
- It stays inactive on orbit legs (:116-119).

**Fence.** AC_WPNav never reads AC_Fence. `AC_WPNav.h:12` includes `AC_Avoid.h`, but no AC_WPNav or SCurve code uses it.
- The fence is checked by `Copter::fence_check` at 25 Hz (ArduCopter/Copter.cpp:154; fence.cpp:39). A breach acts by changing mode, from outside the component.
- The OA planners do read fences (libraries/AC_Avoidance/AP_OADijkstra.cpp, AP_OABendyRuler.cpp). So with OA enabled, fence geometry can reach the navigator indirectly, through the intermediate destinations.

---

## 7. Open questions

1. **Speed and acceleration through the rest of the corner.** The midpoint test checks speed and acceleration only at the midpoint. Whether \|v\| stays within the smaller leg limit and \|a\| within the corner limit for the whole blend is not established by the code.
2. **Corner bound in other cases.** The WP_RADIUS_M bound in 5ii is derived for straight legs whose perpendicular foot stays on the segment. Arc-to-arc and arc-to-straight corners, and very short legs, were not analysed.
3. **Reused preloaded leg.** When the preloaded leg is reused, its geometry is not compared with the newly computed `_destination_ned_m` (AC_WPNav.cpp:414-416). If the two differ, for example through altitude-default round-trips in cm or a mission edit between preload and promotion, the target and the reached/distance reference will disagree.
4. **Infinite speed.** A +inf DO_CHANGE_SPEED value passes both checks. Its effect on `kinematic_limit` and `calculate_path` was not traced.
5. **EKF position or origin reset.** PosControl shifts its targets (`NE_handle_ekf_reset`, AC_PosControl.cpp:1696), and ModeAuto asks for the vehicle to keep its absolute position in WP submodes (mode_auto.cpp:235-262). I did not check whether the navigator's `_origin_ned_m` and `_destination_ned_m` are shifted to match.
6. **Speed limits written by other code.** The S-curve reads its speed limits from PosControl state, which other submodes also write (for example `land_start` writes WP_SPD at mode_auto.cpp:508). The DO_CHANGE_SPEED override is re-applied only when `wp_start` finds the navigator inactive (mode_auto.cpp:468-486). Whether a mid-mission LAND or LOITER_TO_ALT can silently reset a planner-set speed for later legs needs a trace.
7. **Parameter range enforcement.** I did not trace AP_Param's set path to confirm that `@Range` is never enforced at parameter-set time. The tables assume it is not.
8. **SPEED_TYPE values.** The numbers (0 airspeed, 1 groundspeed, 2 climb, 3 descent) come from the generated MAVLink headers, which are not in the clone; they are taken from the MAVLink definition, not the code.
9. **INTERNAL_ERROR consequences.** Whether an INTERNAL_ERROR raised in flight has any effect beyond logging (for example a later arming block) was not traced.
