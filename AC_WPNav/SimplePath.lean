import AP_Math

/-!
# `SimplePath`: the stand-in for ArduPilot's S-curve path generator

**ArduPilot's S-curve path generator `SCurve` (`libraries/AP_Math/SCurve.{h,cpp}`) is NOT
ported.** `SimplePath` replaces it inside the `AC_WPNav` port. It keeps the interface through which
`AC_WPNav` drives `SCurve` (one object per leg, a leg clock, the previous/current/next legs
superposed in `advance_target_along_track`), so the navigator code around it is the C++, but the
profile along a leg is different:

- **Straight legs, trapezoidal speed.** A leg from `origin` to `destination` is a straight line
  flown from rest to rest: constant acceleration `accel_max` up to `vel_max`, constant speed, then
  constant deceleration `accel_max`, or a triangular profile with peak speed
  `sqrt(seg_length * accel_max)` when the leg is too short to reach `vel_max`. `SCurve` uses a
  jerk- and snap-limited seven-segment profile (`SCurve::add_segments`), so the acceleration fed
  forward here jumps by `accel_max` at the phase changes where `SCurve`'s is continuous.
- **Blended corners.** Corners come out of the leg superposition exactly as in `SCurve`
  (`SCurve.cpp:570-607`, ported verbatim below as `advance_target_along_track`): with a fast
  waypoint, the next leg's clock is started while the current leg is still decelerating, once the
  midpoint of the overlap lies within `WP_RADIUS_M` of the corner and its speed and acceleration are
  within limits, and the target is the sum of the two legs' displacements. During the overlap
  one leg decelerates at a constant rate along `d₁` while the other accelerates at a constant rate
  along `d₂`, so the target moves with constant acceleration and the blend is a parabolic arc: the
  quadratic Bézier corner of the earlier navigator `Flight/Navigator.lean` (`Navigator.blend`, the
  point `C + r (u² d₂ - (1 - u)² d₁)`), here with its radius chosen by `SCurve`'s turn test rather
  than by a fixed corner radius.
- **Speed and acceleration limits** are `SCurve`'s: `vel_max = kinematic_limit(chord_ne,
  delta_d, speed_ne, speed_up, speed_down)` and `accel_max = kinematic_limit(chord_ne, delta_d,
  accel_ne, accel_d, accel_d)` (`SCurve.cpp:210-212`), with the argument order of `SCurve`.

Interface mirrored (`SCurve.h`): `init`, `calculate_track` (straight legs only: the `arc_ang_rad`
argument of the C++ is dropped, and the snap and jerk maxima are not used by a trapezoid),
`set_speed_max`, `advance_time`, `move_from_pos_vel_accel`, `move_to_pos_vel_accel`,
`move_from_time_pos_vel_accel`, `advance_target_along_track`, `finished`, `get_time_elapsed`,
`time_end`, `get_time_remaining`, `time_accel_end`, `time_decel_start`, `braking`,
`get_speed_along_track`, `get_accel_along_track`, `get_accel_z_max`, `get_origin_to_destination`.
`valid` stands for the C++ test `num_segs == segments_max`.

Left out: arcs (`MAV_CMD_NAV_ARC_WAYPOINT`, circle legs), `set_origin_speed_max` and
`set_destination_speed_max` (used after spline legs and by `force_stop_at_next_wp`), and the
re-planning of a leg already under way in `set_speed_max` (here a speed change after the leg has
started only updates `vel_max`, which the turn test reads; the profile already being flown is kept).

All arithmetic is `float`, positions `postype_t`, as in `SCurve`.
-/

namespace AC_WPNav

open AP_Math

/-- One leg of the path: the members of `SCurve` that the trapezoid needs. -/
structure SimplePath where
  /-- `seg_delta`: origin to destination, NED m. -/
  seg_delta : Vector3f := {}
  /-- `seg_length`: length of the leg, m. -/
  seg_length : ftype := 0.0
  /-- `vel_max`: speed limit along the leg, m/s. -/
  vel_max : ftype := 0.0
  /-- `accel_max`: acceleration limit along the leg, m/s². -/
  accel_max : ftype := 0.0
  /-- `accel_z_max`: vertical acceleration limit, m/s². -/
  accel_z_max : ftype := 0.0
  /-- Peak speed reached on the leg (`vel_max` unless the leg is too short), m/s. -/
  vel_peak : ftype := 0.0
  /-- End of the acceleration phase, s (`segment[SEG_ACCEL_END].end_time`). -/
  t_accel_end : ftype := 0.0
  /-- End of the constant-speed phase, s (`segment[SEG_DECEL_START].end_time`, `SEG_CONST`). -/
  t_decel_start : ftype := 0.0
  /-- End of the leg, s (`segment[SEG_DECEL_END].end_time`). -/
  t_end : ftype := 0.0
  /-- `time`: the leg clock, s. -/
  time : ftype := 0.0
  /-- `num_segs == segments_max`: a profile has been generated. -/
  valid : Bool := false
deriving Repr, Inhabited

namespace SimplePath

/-- `init()` (`SCurve.cpp:46-63`): an empty leg. -/
def init : SimplePath := {}

/-- Generate the trapezoidal profile for the geometry and limits already stored (the role of
`SCurve::add_segments`). -/
def generate_profile (s : SimplePath) : SimplePath :=
  let a := s.accel_max
  let d_accel := sq s.vel_max / (2.0 * a)
  if 2.0 * d_accel ≤ s.seg_length then
    let t1 := s.vel_max / a
    let t2 := t1 + (s.seg_length - 2.0 * d_accel) / s.vel_max
    { s with vel_peak := s.vel_max, t_accel_end := t1, t_decel_start := t2, t_end := t2 + t1,
             time := 0.0, valid := true }
  else
    let v := safe_sqrt (s.seg_length * a)
    let t1 := v / a
    { s with vel_peak := v, t_accel_end := t1, t_decel_start := t1, t_end := 2.0 * t1,
             time := 0.0, valid := true }

/-- `calculate_track(origin, destination, speed_xy, speed_up, speed_down, accel_xy, accel_z,
accel_c, snap_maximum, jerk_maximum)` (`SCurve.cpp:65-109`, straight geometry `:165-173`,
`generate_path` `:193-235`), straight legs only; `accel_c` and the snap and jerk maxima are not
needed by a trapezoid and are not arguments. A zero-length leg, or non-positive limits, leave the
leg empty (`init`), as in the C++. -/
def calculate_track (origin destination : Vector3p)
    (speed_xy speed_up speed_down accel_xy accel_z : ftype) : SimplePath := Id.run do
  let mut s := init
  -- ensure arguments are positive
  let speed_xy := speed_xy.abs
  let speed_up := speed_up.abs
  let speed_down := speed_down.abs
  let accel_xy := accel_xy.abs
  let accel_z := accel_z.abs
  -- leave track as zero length if origin and destination are equal or if the new track length squared is zero
  let seg_delta := (destination - origin).tofloat
  if seg_delta.is_zero || is_zero seg_delta.length_squared then
    return { s with seg_delta := seg_delta.zero }
  -- set_straight_geometry()
  let length_ne := seg_delta.xy.length
  s := { s with seg_delta := seg_delta, seg_length := seg_delta.length }
  if is_zero s.seg_length then
    return { s with seg_delta := seg_delta.zero }
  -- set speed and acceleration limits from the path (generate_path, :210-212)
  s := { s with vel_max := kinematic_limit_xy_z length_ne seg_delta.z speed_xy speed_up speed_down,
                accel_max := kinematic_limit_xy_z length_ne seg_delta.z accel_xy accel_z accel_z,
                accel_z_max := accel_z }
  -- avoid divide-by zeros. Path will be left as a zero length path
  if !is_positive s.accel_max || !is_positive s.vel_max then
    return init
  return generate_profile s

/-- `time_end()` (`SCurve.cpp:722-728`). -/
def time_end (s : SimplePath) : ftype := if s.valid then s.t_end else 0.0
/-- `get_time_remaining()` (`SCurve.cpp:731-737`). -/
def get_time_remaining (s : SimplePath) : ftype := if s.valid then s.t_end - s.time else 0.0
/-- `time_accel_end()` (`SCurve.cpp:759-765`). -/
def time_accel_end (s : SimplePath) : ftype := if s.valid then s.t_accel_end else 0.0
/-- `time_decel_start()` (`SCurve.cpp:769-775`). -/
def time_decel_start (s : SimplePath) : ftype := if s.valid then s.t_decel_start else 0.0
/-- `braking()` (`SCurve.cpp:749-755`). -/
def braking (s : SimplePath) : Bool := if s.valid then s.time ≥ s.t_decel_start else true
/-- `finished()` (`SCurve.cpp:610-613`). -/
def finished (s : SimplePath) : Bool := s.time ≥ s.time_end
/-- `get_time_elapsed()` (`SCurve.h:141`). -/
def get_time_elapsed (s : SimplePath) : ftype := s.time
/-- `get_speed_along_track()` (`SCurve.h:132`). -/
def get_speed_along_track (s : SimplePath) : ftype := s.vel_max
/-- `get_accel_along_track()` (`SCurve.h:135`). -/
def get_accel_along_track (s : SimplePath) : ftype := s.accel_max
/-- `get_accel_z_max()` (`SCurve.h:138`). -/
def get_accel_z_max (s : SimplePath) : ftype := s.accel_z_max
/-- `get_origin_to_destination()` (`SCurve.h`): `seg_delta`. -/
def get_origin_to_destination (s : SimplePath) : Vector3f := s.seg_delta

/-- `advance_time(dt)` (`SCurve.cpp:778-781`). -/
def advance_time (s : SimplePath) (dt : ftype) : SimplePath :=
  { s with time := MIN (s.time + dt) s.time_end }

/-- The trapezoid at time `t`: `(A, V, P)`, acceleration, speed and distance along the leg (the
role of `SCurve::get_jerk_accel_vel_pos_at_time`, `SCurve.cpp:784-...`). -/
def get_accel_vel_pos_at_time (s : SimplePath) (t : ftype) : ftype × ftype × ftype :=
  if !s.valid then (0.0, 0.0, 0.0)
  else if t < s.t_accel_end then
    (s.accel_max, s.accel_max * t, 0.5 * s.accel_max * sq t)
  else if t < s.t_decel_start then
    (0.0, s.vel_peak, 0.5 * s.accel_max * sq s.t_accel_end + s.vel_peak * (t - s.t_accel_end))
  else if t < s.t_end then
    let tau := s.t_end - t
    (-s.accel_max, s.accel_max * tau, s.seg_length - 0.5 * s.accel_max * sq tau)
  else (0.0, 0.0, s.seg_length)

/-- `project_scurve_onto_track(A1, V1, P1, pos, vel, accel)` (`SCurve.cpp:667-716`), the
straight-segment branch (`:709-715`): adds the leg's displacement, velocity and acceleration. -/
def project_onto_track (s : SimplePath) (A1 V1 P1 : ftype) (pos : Vector3p) (vel accel : Vector3f) :
    Vector3p × Vector3f × Vector3f :=
  if is_zero s.seg_length then (pos, vel, accel)
  else
    let path_unit := s.seg_delta.normalized
    (pos + path_unit.topostype * (topostype P1), vel + path_unit * V1, accel + path_unit * A1)

/-- `move_from_pos_vel_accel(dt, pos, vel, accel)` (`SCurve.cpp:636-643`): advance the clock and
add the displacement from the origin. -/
def move_from_pos_vel_accel (s : SimplePath) (dt : ftype) (pos : Vector3p) (vel accel : Vector3f) :
    SimplePath × Vector3p × Vector3f × Vector3f :=
  let s := s.advance_time dt
  let (A1, V1, P1) := s.get_accel_vel_pos_at_time s.time
  let (pos, vel, accel) := s.project_onto_track A1 V1 P1 pos vel accel
  (s, pos, vel, accel)

/-- `move_to_pos_vel_accel(dt, pos, vel, accel)` (`SCurve.cpp:646-654`): advance the clock and
add the displacement relative to the destination. -/
def move_to_pos_vel_accel (s : SimplePath) (dt : ftype) (pos : Vector3p) (vel accel : Vector3f) :
    SimplePath × Vector3p × Vector3f × Vector3f :=
  let s := s.advance_time dt
  let (A1, V1, P1) := s.get_accel_vel_pos_at_time s.time
  let (pos, vel, accel) := s.project_onto_track A1 V1 P1 pos vel accel
  (s, pos - s.seg_delta.topostype, vel, accel)

/-- `move_from_time_pos_vel_accel(time_now, pos, vel, accel)` (`SCurve.cpp:657-663`). -/
def move_from_time_pos_vel_accel (s : SimplePath) (time_now : ftype) (pos : Vector3p)
    (vel accel : Vector3f) : Vector3p × Vector3f × Vector3f :=
  let (A1, V1, P1) := s.get_accel_vel_pos_at_time time_now
  s.project_onto_track A1 V1 P1 pos vel accel

/-- `advance_target_along_track(prev_leg, next_leg, wp_radius, accel_corner, fast_waypoint, dt,
target_pos, target_vel, target_accel)` (`SCurve.cpp:570-607`), ported line for line; `this` is
the current leg. Returns the three legs, the target and the C++ return value `s_finished`. -/
def advance_target_along_track (this prev_leg next_leg : SimplePath) (wp_radius accel_corner : ftype)
    (fast_waypoint : Bool) (dt : ftype) (target_pos : Vector3p) (target_vel target_accel : Vector3f) :
    (SimplePath × SimplePath × SimplePath) × (Vector3p × Vector3f × Vector3f) × Bool := Id.run do
  let (prev_leg, target_pos, target_vel, target_accel) :=
    prev_leg.move_to_pos_vel_accel dt target_pos target_vel target_accel
  let (this, target_pos, target_vel, target_accel) :=
    this.move_from_pos_vel_accel dt target_pos target_vel target_accel
  let mut s_finished := this.finished
  let mut next_leg := next_leg
  let mut target := (target_pos, target_vel, target_accel)
  -- check for change of leg on fast waypoint
  let time_to_destination := this.get_time_remaining
  if fast_waypoint
      && is_zero next_leg.get_time_elapsed -- The next leg has not started
      && (this.get_time_elapsed ≥ this.time_decel_start) -- The current leg has started the deceleration phase
      && (this.get_time_remaining ≤ next_leg.time_accel_end) -- The current leg will finish before completion of the acceleration phase of the next leg
      then
    -- Calculate the position, velocity and acceleration at the turn mid point
    let turn_pos : Vector3p := -this.get_origin_to_destination.topostype
    let (turn_pos, turn_vel, turn_accel) :=
      this.move_from_time_pos_vel_accel (this.get_time_elapsed + time_to_destination * 0.5) turn_pos {} {}
    let (turn_pos, turn_vel, turn_accel) :=
      next_leg.move_from_time_pos_vel_accel (time_to_destination * 0.5) turn_pos turn_vel turn_accel
    let speed_min := MIN this.get_speed_along_track next_leg.get_speed_along_track
    let accel_z_lim := MIN this.get_accel_z_max next_leg.get_accel_z_max
    if (turn_pos.length < topostype wp_radius) -- The turn mid point is within the waypoint radius
        && (turn_vel.length < speed_min) -- The speed at the turn mid point is less than the minimum speed
        && ((⟨turn_accel.x, turn_accel.y⟩ : Vector2f).length < accel_corner) -- The acceleration at the turn mid point is less than the corner acceleration
        && (turn_accel.z.abs < accel_z_lim) -- The vertical acceleration at the turn mid point is less than the maximum vertical acceleration
        then
      let (n, tp, tv, ta) := next_leg.move_from_pos_vel_accel dt target.1 target.2.1 target.2.2
      next_leg := n
      target := (tp, tv, ta)
  else if !is_zero next_leg.get_time_elapsed then
    let (n, tp, tv, ta) := next_leg.move_from_pos_vel_accel dt target.1 target.2.1 target.2.2
    next_leg := n
    target := (tp, tv, ta)
    if next_leg.get_time_elapsed ≥ this.get_time_remaining then
      -- consider the current leg finished when we have passed half way through the turn between legs
      s_finished := true
  return ((this, prev_leg, next_leg), target, s_finished)

/-- `set_speed_max(speed_xy, speed_up, speed_down)` (`SCurve.cpp:238-...`), reduced: the new
`vel_max` is stored; a leg that has not started is re-planned, a leg under way keeps its profile
(see the header). -/
def set_speed_max (s : SimplePath) (speed_xy speed_up speed_down : ftype) : SimplePath :=
  let speed_xy := speed_xy.abs
  let speed_up := speed_up.abs
  let speed_down := speed_down.abs
  -- return immediately if zero length path
  if !s.valid then s
  else
    let track_speed_max := kinematic_limit_xy_z s.seg_delta.xy.length s.seg_delta.z speed_xy speed_up
      speed_down
    if is_equal s.vel_max track_speed_max then s
    else if is_zero track_speed_max then s
    else
      let s := { s with vel_max := track_speed_max }
      if s.time ≥ s.t_decel_start then s
      else if is_zero s.time then generate_profile s
      else s

end SimplePath

end AC_WPNav
