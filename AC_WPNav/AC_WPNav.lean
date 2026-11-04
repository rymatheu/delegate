import AC_WPNav.SimplePath
import AC_AttitudeControl.AC_PosControl

/-!
# `AC_WPNav`, the waypoint navigator, with `SimplePath` in place of `SCurve`

Mirrors, at ArduPilot 802db19de1, `libraries/AC_WPNav/AC_WPNav.h` (defaults `:15`, inline getters
`:61`, `:108-152`, `:256-266`, `:326`, members `:362-458`) and `AC_WPNav.cpp`: defaults `:8-14`,
`var_info` `:16-114` (as `Params`), `convert_parameters` `:117-162` (as the name aliases of
`Copter.Parameters`), constructor `:164-178`, `wp_and_spline_init_m` `:213-267`,
`set_speed_NE_ms` `:277-293`, `set_speed_up_ms` `:297-304`, `set_speed_down_ms` `:308-315`,
`set_wp_destination_NED_m` `:384-436`, `set_wp_destination_next_NED_m` `:487-515`,
`get_wp_stopping_point_NED_m` `:546-552`, `advance_wp_target_along_track` `:557-656`,
`update_track_with_speed_accel_limits` `:660-677`, `get_wp_distance_to_destination_m` `:687-691`,
`get_wp_bearing_to_destination_rad` `:702-706`, `update_wpnav` `:711-747`, `is_active` `:751-755`,
`calc_scurve_jerk_and_snap` `:1070-1092`.

## The path generator is not ArduPilot's

**The S-curve path generator `SCurve` is NOT ported.** Straight legs with blended corners and a
trapezoidal speed profile stand in for it: `AC_WPNav.SimplePath` (see its header). The three leg
members are therefore named `_path_prev_leg`, `_path_this_leg`, `_path_next_leg` (C++
`_scurve_prev_leg`, ...), and `SimplePath.calculate_track` replaces `SCurve::calculate_track`.
Everything around the path generator is the C++: the speed and acceleration limits handed to
`AC_PosControl`, the leg bookkeeping of `set_wp_destination_NED_m` and
`set_wp_destination_next_NED_m` (previous leg kept for the blend, preloaded next leg, fast
waypoints), and `advance_wp_target_along_track`, whose tracking-error time scaling
(`track_dt_scalar`, read from PosControl's previous-tick position error, velocity estimate,
desired velocity and `NE_get_pos_p().kP()`), terrain speed scaling (`terrain_scaler_D_m` with zero
terrain) and jerk-limited speed offset (`vel_dt_scalar`, `_offset_vel_ms`, `_offset_accel_mss`)
are ported line for line; only the call `_scurve_this_leg.advance_target_along_track(...)` samples
`SimplePath` instead.

`_scurve_jerk_max_msss` and `_scurve_snap_max_mssss` are still computed by
`calc_scurve_jerk_and_snap` (they are state of the C++ object) but `SimplePath` does not use them.

## Conventions

As in `AC_PosControl`: `Params` is the `AP_Param` table with the ArduPilot names at this commit
(Copter prefix `WP_`, `ArduCopter/Parameters.cpp:370`; before 4.7 the prefix was `WPNAV_` and the
speeds were in cm/s, see `Copter.Parameters`), `State` the other members with the C++ names, and
every method a pure function. The navigator holds references to `AC_PosControl` (mutated) and
reads `AC_AttitudeControl`; methods take the PosControl parameters and state and return the new
PosControl state, and take an `Env` with what the C++ reads from the AHRS, the attitude controller,
the motors and the clock (forwarded to the PosControl calls). Parameters that the C++ writes at run
time (`_wp_radius_m`, `_wp_speed_ms` via `set_and_save_ifchanged`, `_wp_jerk_msss` via `set`) have
their RAM value in `State`, initialised from `Params` by `init`.

## Left out

Splines (`_spline_*`, `_this_leg_is_spline`, `_next_leg_is_spline`, `set_spline_*`), arcs and
circle legs (`set_circle_destination_NED_m`, `_this_leg_is_circle`, the `arc_rad` arguments),
terrain-relative altitudes (`_is_terrain_alt` stays false: `get_terrain_D_m`,
`convert_origin_to_alt_frame`, the rangefinder members and `WP_RFND_USE` are not used),
`Location` conversions (`set_wp_destination_loc` and friends; the Copter port hands NED
vectors), the `_cm` wrappers, `force_stop_at_next_wp`, `set_pause`/`_paused` (stays false),
`wp_yaw_set` (unused flag), and the singleton/`AP_Param` plumbing.
-/

namespace AC_WPNav

open AP_Math

/-! ### Defaults, `AC_WPNav.cpp:8-14`, `AC_WPNav.h:15` -/

/-- `WP_SPD_DEFAULT`. -/
def WP_SPD_DEFAULT : ftype := 10.0
/-- `WP_SPD_MIN`. -/
def WP_SPD_MIN : ftype := 0.01
/-- `WP_RADIUS_M_DEFAULT`. -/
def WP_RADIUS_M_DEFAULT : ftype := 2.0
/-- `WP_RADIUS_M_MIN`. -/
def WP_RADIUS_M_MIN : ftype := 0.05
/-- `WP_SPD_UP_DEFAULT`. -/
def WP_SPD_UP_DEFAULT : ftype := 2.5
/-- `WP_SPD_DOWN_DEFAULT`. -/
def WP_SPD_DOWN_DEFAULT : ftype := 1.5
/-- `WP_ACC_Z_DEFAULT`. -/
def WP_ACC_Z_DEFAULT : ftype := 1.0
/-- `WPNAV_ACCELERATION_MS` (`AC_WPNav.h:15`). -/
def WPNAV_ACCELERATION_MS : ftype := 2.5

/-! ### Parameters and state -/

/-- `AC_WPNav::var_info` (`AC_WPNav.cpp:16-114`), Copter prefix `WP_`. -/
structure Params where
  /-- `_rangefinder_use` (`:30`); not used here (no terrain following). -/
  WP_RFND_USE : Int8 := 1
  /-- `_wp_jerk_msss` (`:38`), m/s³. -/
  WP_JERK : ftype := 1.0
  /-- `_terrain_margin_m` (`:46`), m. -/
  WP_TER_MARGIN : ftype := 10.0
  /-- `_wp_speed_ms` (`:57`), m/s. -/
  WP_SPD : ftype := WP_SPD_DEFAULT
  /-- `_wp_radius_m` (`:66`), m. -/
  WP_RADIUS_M : ftype := WP_RADIUS_M_DEFAULT
  /-- `_wp_speed_up_ms` (`:75`), m/s. -/
  WP_SPD_UP : ftype := WP_SPD_UP_DEFAULT
  /-- `_wp_speed_down_ms` (`:84`), m/s. -/
  WP_SPD_DN : ftype := WP_SPD_DOWN_DEFAULT
  /-- `_wp_accel_mss` (`:93`), m/s². -/
  WP_ACC : ftype := WPNAV_ACCELERATION_MS
  /-- `_wp_accel_z_mss` (`:102`), m/s². -/
  WP_ACC_Z : ftype := WP_ACC_Z_DEFAULT
  /-- `_wp_accel_c_mss` (`:111`), m/s²; 0 means twice `WP_ACC`. -/
  WP_ACC_CNR : ftype := 0.0
deriving Repr

/-- `struct wpnav_flags` (`AC_WPNav.h:363-367`); `wp_yaw_set` is not used. -/
structure Flags where
  reached_destination : Bool := false
  fast_waypoint : Bool := false
deriving Repr

/-- The members of `AC_WPNav` (`AC_WPNav.h:362-458`) on the straight-leg path. -/
structure State where
  /-- RAM value of `WP_SPD` (`set_and_save_ifchanged` in `wp_and_spline_init_m`). -/
  _wp_speed_ms : ftype
  /-- RAM value of `WP_RADIUS_M`. -/
  _wp_radius_m : ftype
  /-- RAM value of `WP_JERK` (`_wp_jerk_msss.set` in `wp_and_spline_init_m`). -/
  _wp_jerk_msss : ftype
  _flags : Flags := {}
  _check_wp_speed_change : Bool := false
  _last_wp_speed_ms : ftype := 0.0
  _last_wp_speed_up_ms : ftype := 0.0
  _last_wp_speed_down_ms : ftype := 0.0
  /-- C++ `_scurve_prev_leg` (see the header). -/
  _path_prev_leg : SimplePath := {}
  /-- C++ `_scurve_this_leg`. -/
  _path_this_leg : SimplePath := {}
  /-- C++ `_scurve_next_leg`. -/
  _path_next_leg : SimplePath := {}
  _scurve_jerk_max_msss : ftype := 0.0
  _scurve_snap_max_mssss : ftype := 0.0
  _wp_last_update_ms : UInt32 := 0
  _wp_desired_speed_ne_ms : ftype := 0.0
  _origin_ned_m : Vector3p := {}
  _destination_ned_m : Vector3p := {}
  _next_destination_ned_m : Vector3p := {}
  _track_dt_scalar : ftype := 0.0
  _offset_vel_ms : ftype := 0.0
  _offset_accel_mss : ftype := 0.0
  _paused : Bool := false
  _is_terrain_alt : Bool := false
deriving Repr

/-- What the navigator and the PosControl calls it makes read from the rest of the vehicle. -/
structure Env where
  ahrs : AC_PosControl.AHRSInputs
  att : AC_PosControl.AttitudeControlInputs
  /-- `_attitude_control.get_input_tc()` (`AC_AttitudeControl.h:139`). -/
  att_input_tc : ftype
  motors : AP_Motors.Inputs
  clock : AC_PosControl.Clock

/-- Constructor `AC_WPNav(ahrs, pos_control, attitude_control)` (`AC_WPNav.cpp:164-178`).
Members it does not set are zero (ArduPilot objects are zero-filled). -/
def init (p : Params) : State :=
  { _wp_speed_ms := p.WP_SPD, _wp_radius_m := p.WP_RADIUS_M, _wp_jerk_msss := p.WP_JERK,
    _flags := { reached_destination := false, fast_waypoint := false },
    -- record WP_SPD, WP_SPD_UP, WP_SPD_DN values so we can detect changes
    _last_wp_speed_ms := p.WP_SPD,
    _last_wp_speed_up_ms := p.WP_SPD_UP,
    _last_wp_speed_down_ms := p.WP_SPD_DN.abs }

/-! ### Inline getters, `AC_WPNav.h` -/

/-- `get_terrain_margin_m()` (`.h:61`). -/
def get_terrain_margin_m (p : Params) : ftype := MAX p.WP_TER_MARGIN 0.1
/-- `get_default_speed_NE_ms()` (`.h:108`). -/
def get_default_speed_NE_ms (s : State) : ftype := s._wp_speed_ms
/-- `get_default_speed_up_ms()` (`.h:116`). -/
def get_default_speed_up_ms (p : Params) : ftype := p.WP_SPD_UP
/-- `get_default_speed_down_ms()` (`.h:124`). -/
def get_default_speed_down_ms (p : Params) : ftype := p.WP_SPD_DN.abs
/-- `get_accel_D_mss()` (`.h:132`). -/
def get_accel_D_mss (p : Params) : ftype := p.WP_ACC_Z
/-- `get_wp_acceleration_mss()` (`.h:140`). -/
def get_wp_acceleration_mss (p : Params) : ftype :=
  if is_positive p.WP_ACC then p.WP_ACC else WPNAV_ACCELERATION_MS
/-- `get_corner_acceleration_mss()` (`.h:144`). -/
def get_corner_acceleration_mss (p : Params) : ftype :=
  if is_positive p.WP_ACC_CNR then p.WP_ACC_CNR else 2.0 * get_wp_acceleration_mss p
/-- `get_wp_destination_NED_m()` (`.h:152`). -/
def get_wp_destination_NED_m (s : State) : Vector3p := s._destination_ned_m
/-- `reached_wp_destination()` (`.h:256`). -/
def reached_wp_destination (s : State) : Bool := s._flags.reached_destination
/-- `get_wp_radius_m()` (`.h:266`). -/
def get_wp_radius_m (s : State) : ftype := s._wp_radius_m
/-- `get_yaw_rad()` (`.h:326`): the position controller's yaw target. -/
def get_yaw_rad (psc : AC_PosControl.State) : ftype := AC_PosControl.get_yaw_rad psc
/-- `get_yaw()` (`.h:342`), centidegrees. -/
def get_yaw (psc : AC_PosControl.State) : ftype := rad_to_cd (get_yaw_rad psc)

/-! ### Methods -/

/-- `is_active()` (`AC_WPNav.cpp:751-755`). -/
def is_active (s : State) (clock : AC_PosControl.Clock) : Bool :=
  (clock.millis - s._wp_last_update_ms) < 200

/-- `get_wp_distance_to_destination_m()` (`AC_WPNav.cpp:687-691`). -/
def get_wp_distance_to_destination_m (s : State) (psc : AC_PosControl.State) : ftype :=
  get_horizontal_distance (AC_PosControl.get_pos_estimate_NED_m psc).xy.tofloat s._destination_ned_m.xy.tofloat

/-- `reached_wp_destination_NE()` (`.h:260-262`). -/
def reached_wp_destination_NE (s : State) (psc : AC_PosControl.State) : Bool :=
  get_wp_distance_to_destination_m s psc < s._wp_radius_m

/-- `get_wp_bearing_to_destination_rad()` (`AC_WPNav.cpp:702-706`), clockwise from north. -/
def get_wp_bearing_to_destination_rad (s : State) (psc : AC_PosControl.State) : ftype :=
  get_bearing_rad (AC_PosControl.get_pos_estimate_NED_m psc).xy.tofloat s._destination_ned_m.xy.tofloat

/-- `get_wp_bearing_to_destination_cd()` (`AC_WPNav.cpp:694-698`). -/
def get_wp_bearing_to_destination_cd (s : State) (psc : AC_PosControl.State) : ftype :=
  get_bearing_cd (AC_PosControl.get_pos_estimate_NED_m psc).xy.tofloat s._destination_ned_m.xy.tofloat

/-- `calc_scurve_jerk_and_snap()` (`AC_WPNav.cpp:1070-1092`). The results are not used by
`SimplePath` (header). -/
def calc_scurve_jerk_and_snap (s : State) (env : Env) : State := Id.run do
  let att := env.att
  -- calculate max horizontal jerk based on roll/pitch angular velocity limits
  let mut jerk := MIN (att.get_ang_vel_roll_max_rads * GRAVITY_MSS) (att.get_ang_vel_pitch_max_rads * GRAVITY_MSS)
  if is_zero jerk then
    jerk := s._wp_jerk_msss
  else
    jerk := MIN jerk s._wp_jerk_msss
  -- calculate maximum snap (rate of change of jerk)
  let mut snap := (jerk * M_PI) / (2.0 * MAX env.att_input_tc 0.1)
  -- constrain snap based on roll/pitch angular acceleration capability
  let snap_lim := MIN att.get_accel_roll_max_radss att.get_accel_pitch_max_radss * GRAVITY_MSS
  if is_positive snap_lim then
    snap := MIN snap snap_lim
  -- apply safety margin: reduce snap to 50% of calculated maximum
  snap := snap * 0.5
  return { s with _scurve_jerk_max_msss := jerk, _scurve_snap_max_mssss := snap }

/-- `get_wp_stopping_point_NED_m(stopping_point_ned_m)` (`AC_WPNav.cpp:546-552`). -/
def get_wp_stopping_point_NED_m (psc_p : AC_PosControl.Params) (psc : AC_PosControl.State) : Vector3p :=
  let ne := AC_PosControl.get_stopping_point_NE_m psc_p psc
  let d := AC_PosControl.get_stopping_point_D_m psc_p psc
  ⟨ne.x, ne.y, d⟩

/-- `wp_and_spline_init_m(speed_ms = 0, stopping_point_ned_m = Vector3p{})` (`AC_WPNav.cpp:213-267`). -/
def wp_and_spline_init_m (p : Params) (psc_p : AC_PosControl.Params) (s : State)
    (psc : AC_PosControl.State) (env : Env) (speed_ms : ftype := 0.0)
    (stopping_point_ned_m : Vector3p := {}) : State × AC_PosControl.State := Id.run do
  let mut s := s
  let mut psc := psc
  -- ensure waypoint radius is not below minimum allowed value
  s := { s with _wp_radius_m := MAX s._wp_radius_m WP_RADIUS_M_MIN }
  -- ensure waypoint speed is not below minimum allowed value
  s := { s with _wp_speed_ms := MAX s._wp_speed_ms WP_SPD_MIN }
  -- initialise position controller
  psc := AC_PosControl.D_init_controller_stopping_point psc_p psc env.ahrs env.motors env.att env.clock
  psc := AC_PosControl.NE_init_controller_stopping_point psc_p psc env.ahrs env.att env.clock
  -- determine desired waypoint speed; fallback to default if not provided
  s := { s with _check_wp_speed_change := !is_positive speed_ms }
  s := { s with _wp_desired_speed_ne_ms := if is_positive speed_ms then speed_ms else get_default_speed_NE_ms s }
  s := { s with _wp_desired_speed_ne_ms := MAX s._wp_desired_speed_ne_ms WP_SPD_MIN }
  -- initialise position controller speed and acceleration
  psc := AC_PosControl.NE_set_max_speed_accel_m psc_p psc env.att s._wp_desired_speed_ne_ms (get_wp_acceleration_mss p)
  psc := AC_PosControl.NE_set_correction_speed_accel_m psc_p psc s._wp_desired_speed_ne_ms (get_wp_acceleration_mss p)
  psc := AC_PosControl.D_set_max_speed_accel_m psc_p psc (get_default_speed_down_ms p) (get_default_speed_up_ms p) (get_accel_D_mss p)
  psc := AC_PosControl.D_set_correction_speed_accel_m psc_p psc (get_default_speed_down_ms p) (get_default_speed_up_ms p) (get_accel_D_mss p)
  -- calculate jerk limit if not explicitly set by parameter
  if !is_positive s._wp_jerk_msss then
    s := { s with _wp_jerk_msss := get_wp_acceleration_mss p }
  s := calc_scurve_jerk_and_snap s env
  s := { s with _path_prev_leg := SimplePath.init, _path_this_leg := SimplePath.init,
                _path_next_leg := SimplePath.init }
  s := { s with _track_dt_scalar := 1.0 }
  s := { s with _flags := { reached_destination := true, fast_waypoint := false } }
  -- determine initial origin and destination; fallback to current stopping point if not provided
  let mut stopping_point_ned_m := stopping_point_ned_m
  if stopping_point_ned_m.is_zero then
    stopping_point_ned_m := get_wp_stopping_point_NED_m psc_p psc
  s := { s with _origin_ned_m := stopping_point_ned_m, _destination_ned_m := stopping_point_ned_m }
  s := { s with _is_terrain_alt := false }
  -- initialise velocity profile for terrain margin shaping
  s := { s with _offset_vel_ms := s._wp_desired_speed_ne_ms, _offset_accel_mss := 0.0, _paused := false }
  -- mark as active
  s := { s with _wp_last_update_ms := env.clock.millis }
  return (s, psc)

/-- `update_track_with_speed_accel_limits()` (`AC_WPNav.cpp:660-677`), straight legs. -/
def update_track_with_speed_accel_limits (s : State) (psc : AC_PosControl.State) : State :=
  let vxy := AC_PosControl.NE_get_max_speed_ms psc
  let vup := AC_PosControl.get_max_speed_up_ms psc
  let vdn := AC_PosControl.get_max_speed_down_ms psc
  { s with _path_this_leg := s._path_this_leg.set_speed_max vxy vup vdn,
           _path_next_leg := s._path_next_leg.set_speed_max vxy vup vdn }

/-- `set_speed_NE_ms(speed_ms)` (`AC_WPNav.cpp:277-293`). -/
def set_speed_NE_ms (p : Params) (psc_p : AC_PosControl.Params) (s : State) (psc : AC_PosControl.State)
    (env : Env) (speed_ms : ftype) : State × AC_PosControl.State :=
  -- validate input: speed must be above minimum and current desired speed must be non-zero
  if speed_ms ≥ WP_SPD_MIN && is_positive s._wp_desired_speed_ne_ms then
    -- adjust internal velocity offset to preserve relative motion scaling
    let s := { s with _offset_vel_ms := speed_ms * s._offset_vel_ms / s._wp_desired_speed_ne_ms }
    -- set new desired horizontal speed for waypoint controller
    let s := { s with _wp_desired_speed_ne_ms := speed_ms }
    -- update horizontal shaping and correction constraints
    let psc := AC_PosControl.NE_set_max_speed_accel_m psc_p psc env.att s._wp_desired_speed_ne_ms (get_wp_acceleration_mss p)
    let psc := AC_PosControl.NE_set_correction_speed_accel_m psc_p psc s._wp_desired_speed_ne_ms (get_wp_acceleration_mss p)
    -- update internal trajectory with new limits
    (update_track_with_speed_accel_limits s psc, psc)
  else (s, psc)

/-- `set_speed_up_ms(speed_up_ms)` (`AC_WPNav.cpp:297-304`). -/
def set_speed_up_ms (psc_p : AC_PosControl.Params) (s : State) (psc : AC_PosControl.State)
    (speed_up_ms : ftype) : State × AC_PosControl.State :=
  let psc := AC_PosControl.D_set_max_speed_accel_m psc_p psc (AC_PosControl.get_max_speed_down_ms psc)
    speed_up_ms (AC_PosControl.D_get_max_accel_mss psc)
  (update_track_with_speed_accel_limits s psc, psc)

/-- `set_speed_down_ms(speed_down_ms)` (`AC_WPNav.cpp:308-315`). -/
def set_speed_down_ms (psc_p : AC_PosControl.Params) (s : State) (psc : AC_PosControl.State)
    (speed_down_ms : ftype) : State × AC_PosControl.State :=
  let psc := AC_PosControl.D_set_max_speed_accel_m psc_p psc speed_down_ms
    (AC_PosControl.get_max_speed_up_ms psc) (AC_PosControl.D_get_max_accel_mss psc)
  (update_track_with_speed_accel_limits s psc, psc)

/-- `set_wp_destination_NED_m(destination_ned_m, is_terrain_alt = false, arc_rad = 0)`
(`AC_WPNav.cpp:384-436`), straight legs above the EKF origin (the spline and terrain branches
are not taken: `_this_leg_is_spline` and `_is_terrain_alt` stay false). Returns the C++ `true`
implicitly: this path cannot fail. -/
def set_wp_destination_NED_m (p : Params) (psc_p : AC_PosControl.Params) (s : State)
    (psc : AC_PosControl.State) (env : Env) (destination_ned_m : Vector3p) :
    State × AC_PosControl.State := Id.run do
  let mut s := s
  let mut psc := psc
  -- re-initialise if previous destination has been interrupted
  if !is_active s env.clock || !s._flags.reached_destination then
    let (s', psc') := wp_and_spline_init_m p psc_p s psc env s._wp_desired_speed_ne_ms
    s := s'
    psc := psc'
  s := { s with _path_prev_leg := SimplePath.init }
  -- use previous destination as origin
  s := { s with _origin_ned_m := s._destination_ned_m }
  -- is_terrain_alt == _is_terrain_alt and the current leg is not a spline:
  -- preserve current leg profile to enable blending with new leg
  s := { s with _path_prev_leg := s._path_this_leg }
  -- update destination
  s := { s with _destination_ned_m := destination_ned_m, _is_terrain_alt := false }
  if s._flags.fast_waypoint && !s._path_next_leg.finished then
    -- Reuse preloaded next leg if valid to avoid unnecessary recalculation
    s := { s with _path_this_leg := s._path_next_leg }
  else
    -- Generate a new leg to the new destination (SimplePath in place of SCurve, header)
    let this_leg := SimplePath.calculate_track s._origin_ned_m s._destination_ned_m
      (AC_PosControl.NE_get_max_speed_ms psc) (AC_PosControl.get_max_speed_up_ms psc)
      (AC_PosControl.get_max_speed_down_ms psc) (get_wp_acceleration_mss p) (get_accel_D_mss p)
    s := { s with _path_this_leg := this_leg }
    -- origin_speed_m is zero for a straight leg following a straight leg
  s := { s with _path_next_leg := SimplePath.init }
  s := { s with _next_destination_ned_m := s._next_destination_ned_m.zero }
  s := { s with _flags := { reached_destination := false, fast_waypoint := false } }
  return (s, psc)

/-- `set_wp_destination_next_NED_m(destination_ned_m, is_terrain_alt = false, arc_rad = 0)`
(`AC_WPNav.cpp:487-515`), straight legs. -/
def set_wp_destination_next_NED_m (p : Params) (s : State) (psc : AC_PosControl.State)
    (destination_ned_m : Vector3p) : State :=
  -- Preload next leg with current speed and acceleration constraints
  let next := SimplePath.calculate_track s._destination_ned_m destination_ned_m
    (AC_PosControl.NE_get_max_speed_ms psc) (AC_PosControl.get_max_speed_up_ms psc)
    (AC_PosControl.get_max_speed_down_ms psc) (get_wp_acceleration_mss p) (get_accel_D_mss p)
  -- Enable fast waypoint transition since next leg is known; store the upcoming destination
  { s with _path_next_leg := next, _flags := { s._flags with fast_waypoint := true },
           _next_destination_ned_m := destination_ned_m }

/-- `advance_wp_target_along_track(dt)` (`AC_WPNav.cpp:557-656`). The tracking-error and speed
scaling is the C++ line for line; the target is sampled from `SimplePath` (header). Terrain
altitude is not used, so `terr_offset_d_m = 0` and the function always returns true. -/
def advance_wp_target_along_track (p : Params) (psc_p : AC_PosControl.Params) (s : State)
    (psc : AC_PosControl.State) (dt : ftype) : State × AC_PosControl.State × Bool := Id.run do
  let mut s := s
  let mut psc := psc
  -- calculate terrain offset if using alt-above-terrain frame (_is_terrain_alt is false)
  let terr_offset_d_m : ftype := 0.0
  -- calculate terrain-based velocity scaling factor
  let offset_d_scalar := AC_PosControl.terrain_scaler_D_m psc terr_offset_d_m (get_terrain_margin_m p)
  -- input shape the terrain offset
  psc := AC_PosControl.set_pos_terrain_target_D_m psc terr_offset_d_m
  -- get position controller's post-shaped position offset for use in position error computation
  let psc_pos_offset_ned_m := AC_PosControl.get_pos_offset_NED_m psc
  -- compute current position in NED frame, adjusted to destination frame
  let mut curr_pos_ned_m := AC_PosControl.get_pos_estimate_NED_m psc - psc_pos_offset_ned_m
  curr_pos_ned_m := { curr_pos_ned_m with z := curr_pos_ned_m.z - topostype terr_offset_d_m }
  -- get desired velocity and remove offset
  let mut curr_target_vel_ned_ms := AC_PosControl.get_vel_desired_NED_ms psc
  curr_target_vel_ned_ms := { curr_target_vel_ned_ms with
    z := curr_target_vel_ned_ms.z - AC_PosControl.get_vel_offset_D_ms psc }
  -- scale progression time (track_dt_scalar) based on aircraft's speed alignment with desired path
  let mut track_dt_scalar : ftype := 1.0
  if is_positive curr_target_vel_ned_ms.length_squared then
    let track_direction_neu := curr_target_vel_ned_ms.normalized
    let track_error_ned_m := (AC_PosControl.get_pos_error_NED_m psc).dot track_direction_neu
    let track_velocity_ned_ms := (AC_PosControl.get_vel_estimate_NED_ms psc).dot track_direction_neu
    -- limit time step scalar to [0,1], with 5% buffer
    track_dt_scalar := constrain_float (0.05 + (track_velocity_ned_ms
      - AC_P_2D.kP (AC_PosControl.NE_get_pos_p psc_p psc).1 * track_error_ned_m)
      / curr_target_vel_ned_ms.length) 0.0 1.0
  -- compute velocity scaling (vel_dt_scalar) and apply jerk-limited velocity shaping
  let mut vel_dt_scalar : ftype := 1.0
  if is_positive s._wp_desired_speed_ne_ms then
    s := { s with _offset_vel_ms := update_vel_accel s._offset_vel_ms s._offset_accel_mss dt 0.0 0.0 }
    let vel_input_ms : ftype := if !s._paused then s._wp_desired_speed_ne_ms * offset_d_scalar else 0.0
    let offset_accel_mss := shape_vel_accel vel_input_ms 0.0 s._offset_vel_ms s._offset_accel_mss
      (-get_wp_acceleration_mss p) (get_wp_acceleration_mss p) (AC_PosControl.get_shaping_jerk_NE_msss psc_p)
      dt true
    s := { s with _offset_accel_mss := offset_accel_mss }
    vel_dt_scalar := s._offset_vel_ms / s._wp_desired_speed_ne_ms
  -- apply exponential filter to track_dt_scalar using jerk-based time constant
  let mut track_dt_scalar_tc : ftype := 1.0
  if !is_zero s._wp_jerk_msss then
    track_dt_scalar_tc := get_wp_acceleration_mss p / s._wp_jerk_msss
  s := { s with _track_dt_scalar := s._track_dt_scalar + (track_dt_scalar - s._track_dt_scalar) * (dt / track_dt_scalar_tc) }
  -- compute target state: update target position, velocity and acceleration
  -- (SimplePath in place of `_scurve_this_leg.advance_target_along_track`, header)
  let target_pos_ned_m : Vector3p := s._origin_ned_m
  let ((this_leg, prev_leg, next_leg), (target_pos_ned_m, target_vel_ned_ms, target_accel_ned_mss), s_finished) :=
    SimplePath.advance_target_along_track s._path_this_leg s._path_prev_leg s._path_next_leg s._wp_radius_m
      (get_corner_acceleration_mss p) s._flags.fast_waypoint (s._track_dt_scalar * vel_dt_scalar * dt)
      target_pos_ned_m {} {}
  s := { s with _path_this_leg := this_leg, _path_prev_leg := prev_leg, _path_next_leg := next_leg }
  -- apply scaled acceleration offset along current direction of travel
  let mut accel_offset_ned_mss : Vector3f := {}
  if is_positive target_vel_ned_ms.length_squared then
    let track_direction_neu := target_vel_ned_ms.normalized
    accel_offset_ned_mss := track_direction_neu * s._offset_accel_mss * target_vel_ned_ms.length / s._wp_desired_speed_ne_ms
  let target_vel_ned_ms := target_vel_ned_ms * vel_dt_scalar
  let target_accel_ned_mss := target_accel_ned_mss * sq vel_dt_scalar
  let target_accel_ned_mss := target_accel_ned_mss + accel_offset_ned_mss
  -- send updated position, velocity, and acceleration targets to position controller
  psc := AC_PosControl.set_pos_vel_accel_NED_m psc target_pos_ned_m target_vel_ned_ms target_accel_ned_mss
  -- check if waypoint has been reached based on mode and radius
  if !s._flags.reached_destination then
    if s_finished then
      -- "fast" waypoints are complete once the intermediate point reaches the destination
      if s._flags.fast_waypoint then
        s := { s with _flags := { s._flags with reached_destination := true } }
      else
        -- regular waypoints also require the copter to be within the waypoint radius
        let dist_to_dest_m := (curr_pos_ned_m - s._destination_ned_m).tofloat
        if dist_to_dest_m.length_squared ≤ sq s._wp_radius_m then
          s := { s with _flags := { s._flags with reached_destination := true } }
  -- successfully advanced along track
  return (s, psc, true)

/-- `update_wpnav()` (`AC_WPNav.cpp:711-747`): WP_SPD change checks, `advance_wp_target_along_track`
with PosControl's `dt`, then `_pos_control.NE_update_controller()`. Returns the C++ return value
too (always true here, no terrain). -/
def update_wpnav (p : Params) (psc_p : AC_PosControl.Params) (s : State) (psc : AC_PosControl.State)
    (env : Env) : State × AC_PosControl.State × Bool := Id.run do
  let mut s := s
  let mut psc := psc
  -- check for changes in WP_SPD parameter (horizontal speed target)
  if s._check_wp_speed_change then
    if !is_equal s._wp_speed_ms s._last_wp_speed_ms then
      -- apply new WP_SPD value
      let (s', psc') := set_speed_NE_ms p psc_p s psc env (get_default_speed_NE_ms s)
      s := { s' with _last_wp_speed_ms := s'._wp_speed_ms }
      psc := psc'
  -- check for climb and descent speed updates
  if !is_equal p.WP_SPD_UP s._last_wp_speed_up_ms then
    let (s', psc') := set_speed_up_ms psc_p s psc (get_default_speed_up_ms p)
    s := { s' with _last_wp_speed_up_ms := p.WP_SPD_UP }
    psc := psc'
  if !is_equal p.WP_SPD_DN s._last_wp_speed_down_ms then
    let (s', psc') := set_speed_down_ms psc_p s psc (get_default_speed_down_ms p)
    s := { s' with _last_wp_speed_down_ms := p.WP_SPD_DN }
    psc := psc'
  -- advance the waypoint target based on current position and timing
  let (s', psc', ret) := advance_wp_target_along_track p psc_p s psc (AC_PosControl.get_dt_s psc)
  s := s'
  psc := psc'
  -- run the horizontal position controller
  psc := AC_PosControl.NE_update_controller psc_p psc env.ahrs env.att env.clock
  -- record update time for is_active()
  s := { s with _wp_last_update_ms := env.clock.millis }
  return (s, psc, ret)

end AC_WPNav
