import AP_Math.vector3

/-!
# `AP_Math/control.h` and `control.cpp`, controller helpers

Mirrors `libraries/AP_Math/control.cpp` at ArduPilot 802db19de1:
`:46-59` `update_vel_accel`, `:67-78` `update_pos_vel_accel`, `:86-98` `update_vel_accel_xy`,
`:106-121` `update_pos_vel_accel_xy`, `:127-142` `shape_accel`, `:148-174` `shape_accel_xy` (both),
`:182-222` `shape_vel_accel`, `:230-259` `shape_vel_accel_xy`, `:269-346` `shape_pos_vel_accel`,
`:356-422` `shape_pos_vel_accel_xy`, `:433-441` `shape_angle_vel_accel`, `:449-501`
`limit_accel_xy`, `:512-568` `limit_accel_corner_xy`, `:575-610` `sqrt_controller`, `:616-625`
`sqrt_controller` (vector), `:630-659` `inv_sqrt_controller`, `:673-706` `sqrt_controller_accel`,
`:712-716` `stopping_distance`, `:734-804` `kinematic_limit` (both), `:823-849`
`angle_rad_to_accel_mss`, `angle_deg_to_accel_mss`, `accel_mss_to_angle_rad`,
`accel_mss_to_angle_deg`.

These are all the `control.cpp` functions that `AC_PosControl.cpp`, `AC_AttitudeControl.cpp`,
`AC_AttitudeControl_Multi.cpp`, `AC_WPNav.cpp`, `AC_P_1D.cpp`, `AC_P_2D.cpp` and
`ArduCopter/mode_auto.cpp` call, plus `limit_accel_corner_xy`, which the shaping functions call.

Conventions. C++ reference outputs become return values, in parameter order, followed by the C++
return value if any: `update_pos_vel_accel` returns `(pos, vel)`, `shape_*` return the new
`accel`, `limit_accel_xy` returns `(accel, bool)`. Implicit `float`→`postype_t` conversions at call
sites are written `topostype`, and `postype_t`→`float` narrowing `tofloat`. `INTERNAL_ERROR` on a
failed sanity check is dropped; the early `return` (output unchanged) is kept. Overloads:
`sqrt_controller(const Vector2f&, ...)` is `sqrt_controller_xy`, `shape_accel_xy(const Vector3f&,
...)` is `shape_accel_xy_vec3`, and `kinematic_limit(float dir_xy, float dir_z, ...)` is
`kinematic_limit_xy_z`. No loops occur, so no fuel is needed.

Left out (not called by the cascade): `input_expo`, `rc_input_to_roll_pitch_rad`, and the unused
`CORNER_ACCELERATION_RATIO` macro (`:28`).
-/

namespace AP_Math

/-- `LIMIT_ACCEL_XY_MIN_REF` (`control.cpp:38`). -/
def LIMIT_ACCEL_XY_MIN_REF : Float32 := 0.25

/-- `update_vel_accel(float& vel, accel, dt, limit, vel_error)`; returns the new `vel`. -/
def update_vel_accel (vel accel dt limit vel_error : Float32) : Float32 :=
  let delta_vel := accel * dt
  let delta_vel :=
    if is_positive (delta_vel * limit) && is_positive (vel_error * limit) then
      if is_negative (vel * limit) then constrain_float delta_vel (-vel.abs) vel.abs
      else 0.0
    else delta_vel
  vel + delta_vel

/-- `update_pos_vel_accel(postype_t& pos, float& vel, ...)`; returns `(pos, vel)`. -/
def update_pos_vel_accel (pos : postype) (vel accel dt limit pos_error vel_error : Float32) :
    postype × Float32 :=
  let delta_pos := vel * dt + accel * 0.5 * sq dt
  let delta_pos :=
    if is_positive (delta_pos * limit) && is_positive (pos_error * limit) then 0.0 else delta_pos
  let pos := pos + topostype delta_pos
  (pos, update_vel_accel vel accel dt limit vel_error)

/-- `update_vel_accel_xy(Vector2f& vel, accel, dt, limit, vel_error)`; returns the new `vel`. -/
def update_vel_accel_xy (vel accel : Vector2f) (dt : Float32) (limit vel_error : Vector2f) :
    Vector2f :=
  let delta_vel := accel * dt
  let delta_vel :=
    if !limit.is_zero && !delta_vel.is_zero then
      if is_positive (delta_vel * limit) && is_positive (vel_error * limit)
          && !is_negative (vel * limit) then delta_vel.zero
      else delta_vel
    else delta_vel
  vel + delta_vel

/-- `update_pos_vel_accel_xy(Vector2p& pos, Vector2f& vel, ...)`; returns `(pos, vel)`. -/
def update_pos_vel_accel_xy (pos : Vector2p) (vel accel : Vector2f) (dt : Float32)
    (limit pos_error vel_error : Vector2f) : Vector2p × Vector2f :=
  let delta_pos := vel * dt + accel * (0.5 : Float32) * sq dt
  let delta_pos :=
    if !is_zero limit.length_squared then
      if is_positive (delta_pos * limit) && is_positive (pos_error * limit) then delta_pos.zero
      else delta_pos
    else delta_pos
  let pos := pos + delta_pos.topostype
  (pos, update_vel_accel_xy vel accel dt limit vel_error)

/-- `shape_accel(accel_desired, float& accel, jerk_max, dt)`; returns the new `accel`. -/
def shape_accel (accel_desired accel jerk_max dt : Float32) : Float32 :=
  if !is_positive jerk_max then accel
  else if is_positive dt then
    let accel_delta := accel_desired - accel
    let accel_delta := constrain_float accel_delta (-jerk_max * dt) (jerk_max * dt)
    accel + accel_delta
  else accel

/-- `shape_accel_xy(const Vector2f& accel_desired, Vector2f& accel, jerk_max, dt)`. -/
def shape_accel_xy (accel_desired accel : Vector2f) (jerk_max dt : Float32) : Vector2f :=
  if !is_positive jerk_max then accel
  else if is_positive dt then
    let accel_delta := accel_desired - accel
    let accel_delta := (accel_delta.limit_length (jerk_max * dt)).1
    accel + accel_delta
  else accel

/-- `shape_accel_xy(const Vector3f& accel_desired, Vector3f& accel, jerk_max, dt)`: shapes the
x and y components, leaves `accel.z`. -/
def shape_accel_xy_vec3 (accel_desired accel : Vector3f) (jerk_max dt : Float32) : Vector3f :=
  let accel_desired_2f : Vector2f := ⟨accel_desired.x, accel_desired.y⟩
  let accel_2f : Vector2f := ⟨accel.x, accel.y⟩
  let accel_2f := shape_accel_xy accel_desired_2f accel_2f jerk_max dt
  { accel with x := accel_2f.x, y := accel_2f.y }

/-- `sqrt_controller(float error, p, second_ord_lim, dt)`: linear `error*p` inside
`second_ord_lim / sq(p)`, square-root shaped beyond, clamped to `±|error|/dt` when `dt > 0`. -/
def sqrt_controller (error p second_ord_lim dt : Float32) : Float32 :=
  let correction_rate :=
    if is_negative second_ord_lim || is_zero second_ord_lim then
      error * p
    else if is_zero p then
      if is_positive error then safe_sqrt (2.0 * second_ord_lim * (error))
      else if is_negative error then -safe_sqrt (2.0 * second_ord_lim * (-error))
      else 0.0
    else
      let linear_dist := second_ord_lim / sq p
      if error > linear_dist then
        safe_sqrt (2.0 * second_ord_lim * (error - (linear_dist / 2.0)))
      else if error < -linear_dist then
        -safe_sqrt (2.0 * second_ord_lim * (-error - (linear_dist / 2.0)))
      else
        error * p
  if is_positive dt then
    constrain_float correction_rate (-error.abs / dt) (error.abs / dt)
  else
    correction_rate

/-- `sqrt_controller(const Vector2f& error, p, second_ord_lim, dt)`. -/
def sqrt_controller_xy (error : Vector2f) (p second_ord_lim dt : Float32) : Vector2f :=
  let error_length := error.length
  if !is_positive error_length then {}
  else
    let correction_length := sqrt_controller error_length p second_ord_lim dt
    error * (correction_length / error_length)

/-- `inv_sqrt_controller(output, p, D_max)`: the error that `sqrt_controller` maps to `output`. -/
def inv_sqrt_controller (output p D_max : Float32) : Float32 :=
  if is_positive D_max && is_zero p then
    (output * output) / (2.0 * D_max)
  else if (is_negative D_max || is_zero D_max) && !is_zero p then
    output / p
  else if (is_negative D_max || is_zero D_max) && is_zero p then
    0.0
  else
    let linear_velocity := D_max / p
    if output.abs < linear_velocity then
      output / p
    else
      let linear_dist := D_max / sq p
      let stopping_dist := (linear_dist * 0.5) + sq output / (2.0 * D_max)
      if is_positive output then stopping_dist else -stopping_dist

/-- `sqrt_controller_accel(error, rate_cmd, rate_state, p, second_ord_lim)`: the rate of change
of `sqrt_controller`'s output implied by the closing rate `rate_state`. -/
def sqrt_controller_accel (error rate_cmd rate_state p second_ord_lim : Float32) : Float32 :=
  if !is_positive (rate_cmd * rate_state) then 0.0
  else if !is_positive second_ord_lim then -p * rate_state
  else if !is_positive p then
    if is_zero rate_cmd then 0.0
    else -(second_ord_lim / rate_cmd.abs) * rate_state
  else
    let linear_dist := second_ord_lim / sq p
    if error.abs ≤ linear_dist then -p * rate_state
    else if is_zero rate_cmd then 0.0
    else -(second_ord_lim / rate_cmd.abs) * rate_state

/-- `stopping_distance(velocity, p, accel_max)`. -/
def stopping_distance (velocity p accel_max : Float32) : Float32 :=
  inv_sqrt_controller velocity p accel_max

/-- `limit_accel_corner_xy(const Vector2f& vel, Vector2f& accel, accel_max)`; returns
`(accel, bool)`. Braking along `vel` has priority; otherwise cross-track has priority. -/
def limit_accel_corner_xy (vel accel : Vector2f) (accel_max : Float32) : Vector2f × Bool :=
  if !is_positive accel_max then (accel, false)
  else if vel.is_zero then accel.limit_length accel_max
  else
    let accel := (accel.limit_length (2.0 * accel_max)).1
    let vel_unit := vel.normalized
    let accel_dir_scalar := accel.dot vel_unit
    let accel_dir := vel_unit * accel_dir_scalar
    let accel_cross := accel - accel_dir
    if is_positive accel_dir_scalar then
      let accel_cross_mag := MIN accel_cross.length accel_max
      let accel_along_max := safe_sqrt (sq accel_max - sq accel_cross_mag)
      let accel_cross := (accel_cross.limit_length accel_max).1
      let accel_dir := (accel_dir.limit_length accel_along_max).1
      (accel_cross + accel_dir, true)
    else
      let accel_dir_scalar := MAX accel_dir_scalar (-accel_max)
      let accel_dir := vel_unit * accel_dir_scalar
      let accel_cross_max := safe_sqrt (sq accel_max - sq accel_dir_scalar)
      let accel_cross := (accel_cross.limit_length accel_cross_max).1
      (accel_cross + accel_dir, true)

/-- `limit_accel_xy(const Vector2f& vel_norm, Vector2f& accel, accel_max)`; returns
`(accel, bool)`. Cross-track priority, faded to a plain magnitude limit below
`LIMIT_ACCEL_XY_MIN_REF`. -/
def limit_accel_xy (vel_norm accel : Vector2f) (accel_max : Float32) : Vector2f × Bool :=
  if !is_positive accel_max then (accel, false)
  else if accel.length_squared ≤ sq accel_max then (accel, false)
  else
    let accel_isotropic := (accel.limit_length accel_max).1
    let ref_mag := vel_norm.length
    if !is_positive ref_mag then (accel_isotropic, true)
    else
      let ref_unit := vel_norm / ref_mag
      let accel_dir : Float32 := ref_unit * accel
      let accel_cross := accel - (ref_unit * accel_dir)
      let (accel_cross, limited) := accel_cross.limit_length accel_max
      let accel_dir :=
        if limited then 0.0
        else
          let accel_max_dir := safe_sqrt (sq accel_max - accel_cross.length_squared)
          constrain_float accel_dir (-accel_max_dir) accel_max_dir
      let accel_prioritised := accel_cross + ref_unit * accel_dir
      let prioritise_ratio := constrain_float (ref_mag / LIMIT_ACCEL_XY_MIN_REF) 0.0 1.0
      (accel_isotropic * (1.0 - prioritise_ratio) + accel_prioritised * prioritise_ratio, true)

/-- `shape_vel_accel(vel_desired, accel_desired, vel, float& accel, accel_min, accel_max,
jerk_max, dt, limit_total_accel)`; returns the new `accel`. -/
def shape_vel_accel (vel_desired accel_desired vel accel accel_min accel_max jerk_max dt : Float32)
    (limit_total_accel : Bool) : Float32 :=
  if !is_negative accel_min || !is_positive accel_max || !is_positive jerk_max then accel
  else
    let vel_error := vel_desired - vel
    let KPa := if is_positive vel_error then jerk_max / accel_max else jerk_max / (-accel_min)
    let accel_target := sqrt_controller vel_error KPa jerk_max dt
    let accel_target := constrain_float accel_target accel_min accel_max
    let accel_target := accel_target + accel_desired
    let accel_target :=
      if limit_total_accel then constrain_float accel_target accel_min accel_max else accel_target
    shape_accel accel_target accel jerk_max dt

/-- `shape_vel_accel_xy(vel_desired, accel_desired, vel, Vector2f& accel, accel_max, jerk_max,
dt, limit_total_accel)`; returns the new `accel`. -/
def shape_vel_accel_xy (vel_desired accel_desired vel accel : Vector2f)
    (accel_max jerk_max dt : Float32) (limit_total_accel : Bool) : Vector2f :=
  if !is_positive accel_max || !is_positive jerk_max then accel
  else
    let KPa := jerk_max / accel_max
    let vel_error := vel_desired - vel
    let accel_target := sqrt_controller_xy vel_error KPa jerk_max dt
    let accel_target := (limit_accel_corner_xy vel accel_target accel_max).1
    let accel_target := accel_target + accel_desired
    let accel_target :=
      if limit_total_accel then (accel_target.limit_length accel_max).1 else accel_target
    shape_accel_xy accel_target accel jerk_max dt

/-- `shape_pos_vel_accel(pos_desired, vel_desired, accel_desired, pos, vel, float& accel,
vel_min, vel_max, accel_min, accel_max, jerk_max, dt, limit_total)`; returns the new `accel`. -/
def shape_pos_vel_accel (pos_desired : postype) (vel_desired accel_desired : Float32)
    (pos : postype) (vel accel vel_min vel_max accel_min accel_max jerk_max dt : Float32)
    (limit_total : Bool) : Float32 :=
  if is_positive vel_min || is_negative vel_max || !is_negative accel_min
      || !is_positive accel_max || !is_positive jerk_max then accel
  else
    let pos_error : Float32 := tofloat (pos_desired - pos)
    let (accel_lim, k_v) :=
      if is_positive pos_error then
        let accel_lim := -accel_min
        (accel_lim, jerk_max / accel_lim)
      else
        let accel_lim := accel_max
        (accel_lim, jerk_max / accel_lim)
    let vel_corr := vel - vel_desired
    let vel_corr_cmd := sqrt_controller pos_error k_v accel_lim dt
    let accel_corr_cmd := sqrt_controller_accel pos_error vel_corr_cmd vel_corr k_v accel_lim
    let vel_corr_cmd := vel_corr_cmd + accel_corr_cmd / k_v
    let vel_corr_cmd := if is_negative vel_min then MAX vel_corr_cmd vel_min else vel_corr_cmd
    let vel_corr_cmd := if is_positive vel_max then MIN vel_corr_cmd vel_max else vel_corr_cmd
    let vel_target := vel_desired + vel_corr_cmd
    let vel_target :=
      if limit_total then
        let vel_target := if is_negative vel_min then MAX vel_target vel_min else vel_target
        if is_positive vel_max then MIN vel_target vel_max else vel_target
      else vel_target
    let accel_target := (vel_target - vel) * k_v
    let accel_target := constrain_float accel_target accel_min accel_max
    let accel_target := accel_target + accel_desired
    let accel_target :=
      if limit_total then constrain_float accel_target accel_min accel_max else accel_target
    shape_accel accel_target accel jerk_max dt

/-- `shape_pos_vel_accel_xy(pos_desired, vel_desired, accel_desired, pos, vel, Vector2f& accel,
vel_max, accel_max, jerk_max, dt, limit_total)`; returns the new `accel`. -/
def shape_pos_vel_accel_xy (pos_desired : Vector2p) (vel_desired accel_desired : Vector2f)
    (pos : Vector2p) (vel accel : Vector2f) (vel_max accel_max jerk_max dt : Float32)
    (limit_total : Bool) : Vector2f :=
  if is_negative vel_max || !is_positive accel_max || !is_positive jerk_max then accel
  else
    let k_v := jerk_max / accel_max
    let vel_corr_cmd : Vector2f := {}
    let pos_error := (pos_desired - pos).tofloat
    let pos_error_length := pos_error.length
    let vel_corr_cmd :=
      if is_positive pos_error_length then
        let vel_corr_proj := (vel - vel_desired).dot pos_error / pos_error_length
        let vel_corr_cmd_length := sqrt_controller pos_error_length k_v accel_max dt
        let accel_corr_cmd_length :=
          sqrt_controller_accel pos_error_length vel_corr_cmd_length vel_corr_proj k_v accel_max
        let vel_corr_cmd_length := vel_corr_cmd_length + accel_corr_cmd_length / k_v
        let vel_corr_cmd_length :=
          if is_positive vel_max then constrain_float vel_corr_cmd_length (-vel_max) vel_max
          else vel_corr_cmd_length
        pos_error * (vel_corr_cmd_length / pos_error_length)
      else vel_corr_cmd
    let vel_target := vel_desired + vel_corr_cmd
    let vel_target :=
      if limit_total && is_positive vel_max then (vel_target.limit_length vel_max).1
      else vel_target
    let accel_target := (vel_target - vel) * k_v
    let accel_target := (limit_accel_corner_xy vel accel_target accel_max).1
    let accel_target := accel_target + accel_desired
    let accel_target :=
      if limit_total then (accel_target.limit_length accel_max).1 else accel_target
    shape_accel_xy accel_target accel jerk_max dt

/-- `shape_angle_vel_accel(angle_desired, angle_vel_desired, angle_accel_desired, angle,
angle_vel, float& angle_accel, angle_vel_min, angle_vel_max, angle_accel_max, angle_jerk_max, dt,
limit_total)`; returns the new `angle_accel`. The two angles are widened to `postype_t` at the call
to `shape_pos_vel_accel`, as in the C++. -/
def shape_angle_vel_accel (angle_desired angle_vel_desired angle_accel_desired angle angle_vel
    angle_accel angle_vel_min angle_vel_max angle_accel_max angle_jerk_max dt : Float32)
    (limit_total : Bool) : Float32 :=
  let angle_desired_wrapped := angle + wrap_PI (angle_desired - angle)
  shape_pos_vel_accel (topostype angle_desired_wrapped) angle_vel_desired angle_accel_desired
    (topostype angle) angle_vel angle_accel angle_vel_min angle_vel_max (-angle_accel_max)
    angle_accel_max angle_jerk_max dt limit_total

/-- `kinematic_limit(float dir_xy, float dir_z, max_xy, max_z_neg, max_z_pos)`: the largest
`M ≥ 0` with `M·|unit.xy| ≤ max_xy` and `-max_z_neg ≤ M·unit.z ≤ max_z_pos`. -/
def kinematic_limit_xy_z (dir_xy dir_z max_xy max_z_neg max_z_pos : Float32) : Float32 :=
  if is_negative dir_xy || !is_positive max_xy || !is_positive max_z_pos
      || !is_positive max_z_neg then 0.0
  else
    let dir_length := safe_sqrt (sq dir_xy + sq dir_z)
    if !is_positive dir_length then 0.0
    else if is_zero dir_xy then (if is_positive dir_z then max_z_pos else max_z_neg)
    else if is_zero dir_z then max_xy
    else
      let dir_xy := dir_xy / dir_length
      let dir_z := dir_z / dir_length
      let slope := dir_z / dir_xy
      if is_positive slope then
        if slope < max_z_pos / max_xy then max_xy / dir_xy
        else max_z_pos / dir_z
      else if -slope < max_z_neg / max_xy then max_xy / dir_xy
      else -max_z_neg / dir_z

/-- `kinematic_limit(Vector3f direction, max_xy, max_z_neg, max_z_pos)`. -/
def kinematic_limit (direction : Vector3f) (max_xy max_z_neg max_z_pos : Float32) : Float32 :=
  let dir_xy := direction.xy.length
  kinematic_limit_xy_z dir_xy direction.z max_xy max_z_neg max_z_pos

/-- `angle_rad_to_accel_mss`: `GRAVITY_MSS * tanf(angle_rad)`. -/
def angle_rad_to_accel_mss (angle_rad : Float32) : Float32 := GRAVITY_MSS * angle_rad.tan

/-- `angle_deg_to_accel_mss`. -/
def angle_deg_to_accel_mss (angle_deg : Float32) : Float32 :=
  angle_rad_to_accel_mss (radians angle_deg)

/-- `accel_mss_to_angle_rad`: `atanf(accel_mss/GRAVITY_MSS)`. -/
def accel_mss_to_angle_rad (accel_mss : Float32) : Float32 := (accel_mss / GRAVITY_MSS).atan

/-- `accel_mss_to_angle_deg`. -/
def accel_mss_to_angle_deg (accel_mss : Float32) : Float32 :=
  degrees (accel_mss_to_angle_rad accel_mss)

end AP_Math
