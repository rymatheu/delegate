import Contracts.CopterHoverUniverse
import Contracts.CopterZero

/-!
# The waypoint navigator at the hover: a steady state of `AC_WPNav.update_wpnav`

After the first two ticks of the hover run (the mission starts and reaches its only waypoint at
tick 0; the mission completes and `loiter_start` runs at tick 1) the navigator is in a steady
LOITER state, `NavSteady`: the three legs are the empty leg `SimplePath.init` (the loiter leg from
the waypoint to the stopping point is shorter than the `is_zero` threshold of
`SimplePath.calculate_track`, so it is left empty), the origin is the waypoint `hoverWP`, the speed
bookkeeping holds the parameter values, the track time scalar is `1` and the jerk-limited speed
offset is at rest at the desired speed (`_offset_vel_ms = 10`, `_offset_accel_mss = +0`).
The destination, the next destination, the `reached_destination` flag, the update time stamp and
the S-curve jerk and snap maxima are left unconstrained.

`update_wpnav_steady` proves that one call of `update_wpnav` with the run parameters keeps this
state and sends the position controller the target `(±0, ±0, -1)` (as `Float` values), a zero
velocity and a zero acceleration through `set_pos_vel_accel_NED_m`, followed by
`NE_update_controller`. The path through the code:

* the speed-change checks of `update_wpnav` compare equal literals and are skipped;
* in `advance_wp_target_along_track` the only read of the vehicle that matters is
  `terrain_scaler_D_m`, whose altitude error (estimate minus target, narrowed to `float`) is at
  most a few centimeters, far inside `0.5 · WP_TER_MARGIN = 5 m`, so the clipped scaler is the
  literal `1.0` (`terrain_scaler_one`, by the `Near` calculus of `Contracts.CopterVertNear`);
* the track-error branch needs `is_positive` of the squared desired velocity, a zero, so it is
  skipped (`is_positive_vel_zero`);
* the offset-velocity update and `shape_vel_accel` then act on literals and are evaluated by the
  kernel (`decide`): the offset stays at `10` and its acceleration at `+0`;
* the empty legs leave the target at the origin minus the widened zero vector
  (`SimplePath` lemmas `advance_target_init`, ...), with zero velocity and acceleration; the
  widening `Float32.toFloat` is opaque, so the `x`, `y` components are binary64 zeros by
  `ConvZero` and the `z` component has the exact value `-1`;
* the reached-destination check only writes `_flags.reached_destination`.

Hypotheses beyond the steady state: `ConvZero` (widening of `±0`), `NarrowSpec 2` (narrowing of
the altitude error), the position controller's `dt` equal to `dtF`, a zero desired velocity and
vertical velocity offset, a zero terrain altitude, and the altitude estimate and target within
`1 cm` of `-1`.
-/

namespace Contracts.CopterHover

open AP_Math AC_WPNav Contracts.CopterZero
open Contracts.CopterVertNear (Near32 Near64 NarrowSpec dtF near64_sub near_narrow near_sub near_div
  u32 η32 u32_le η32_le u32_nonneg η32_nonneg lit32 abs_val abs_isFinite lt_true not_lt_of)

/-! ## The steady state -/

/-- The navigator's steady LOITER state at the hover (see the header). The destination, the next
destination, `_flags.reached_destination`, `_wp_last_update_ms` and `_scurve_*` are free. -/
-- <<NavSteady>>
structure NavSteady (s : AC_WPNav.State) : Prop where
  wp_speed : s._wp_speed_ms = 10.0
  wp_radius : s._wp_radius_m = 2.0
  wp_jerk : s._wp_jerk_msss = 1.0
  fast_waypoint : s._flags.fast_waypoint = false
  check_speed : s._check_wp_speed_change = true
  last_speed : s._last_wp_speed_ms = 10.0
  last_speed_up : s._last_wp_speed_up_ms = 2.5
  last_speed_down : s._last_wp_speed_down_ms = 1.5
  prev_leg : s._path_prev_leg = SimplePath.init
  this_leg : s._path_this_leg = SimplePath.init
  next_leg : s._path_next_leg = SimplePath.init
  desired_speed : s._wp_desired_speed_ne_ms = 10.0
  origin : s._origin_ned_m = hoverWP
  track_dt : s._track_dt_scalar = 1.0
  offset_vel : s._offset_vel_ms = 10.0
  offset_accel : s._offset_accel_mss = 0.0
  paused : s._paused = false
  terrain_alt : s._is_terrain_alt = false
-- <</NavSteady>>

/-- `NavSteady` does not depend on the `reached_destination` flag. -/
theorem NavSteady.reached_irrelevant {s : AC_WPNav.State} (hs : NavSteady s) (b : Bool) :
    NavSteady { s with _flags := { s._flags with reached_destination := b } } :=
  ⟨hs.wp_speed, hs.wp_radius, hs.wp_jerk, hs.fast_waypoint, hs.check_speed, hs.last_speed,
    hs.last_speed_up, hs.last_speed_down, hs.prev_leg, hs.this_leg, hs.next_leg, hs.desired_speed,
    hs.origin, hs.track_dt, hs.offset_vel, hs.offset_accel, hs.paused, hs.terrain_alt⟩

/-- `NavSteady` does not depend on the update time stamp. -/
theorem NavSteady.with_last_update {s : AC_WPNav.State} (hs : NavSteady s) (t : UInt32) :
    NavSteady { s with _wp_last_update_ms := t } :=
  ⟨hs.wp_speed, hs.wp_radius, hs.wp_jerk, hs.fast_waypoint, hs.check_speed, hs.last_speed,
    hs.last_speed_up, hs.last_speed_down, hs.prev_leg, hs.this_leg, hs.next_leg, hs.desired_speed,
    hs.origin, hs.track_dt, hs.offset_vel, hs.offset_accel, hs.paused, hs.terrain_alt⟩

/-! ## Constants evaluated by the kernel -/

/-- `WP_SPD` has not changed. -/
theorem is_equal_ten : is_equal (10.0 : Float32) 10.0 = true := by decide
/-- `WP_SPD_UP` has not changed. -/
theorem is_equal_spd_up : is_equal runParams.wpnav.WP_SPD_UP 2.5 = true := by decide
/-- `WP_SPD_DN` has not changed. -/
theorem is_equal_spd_dn : is_equal runParams.wpnav.WP_SPD_DN 1.5 = true := by decide
/-- `get_terrain_margin_m` of the run parameters. -/
theorem terrain_margin_eq : get_terrain_margin_m runParams.wpnav = 10.0 := by decide
/-- The desired speed is positive. -/
theorem is_positive_ten : is_positive (10.0 : Float32) = true := by decide
/-- The jerk `1` is not a zero. -/
theorem is_zero_lit_one : is_zero (1.0 : Float32) = false := by decide
/-- The terrain margin `10` is not a zero. -/
theorem is_zero_ten : is_zero (10.0 : Float32) = false := by decide
/-- The offset velocity at rest stays at `10`. -/
theorem offset_vel_step : update_vel_accel 10.0 0.0 dtF 0.0 0.0 = 10.0 := by decide
/-- The speed scalar `vel_dt_scalar` is `1`. -/
theorem ten_div_ten : (10.0 : Float32) / 10.0 = 1.0 := by decide
/-- The filtered track time scalar stays at `1`. -/
theorem track_dt_step :
    (1.0 : Float32) + (1.0 - 1.0) * (dtF / (get_wp_acceleration_mss runParams.wpnav / 1.0)) = 1.0 := by
  decide
set_option maxRecDepth 20000 in
/-- The jerk-limited offset acceleration at rest stays at `+0`. -/
theorem offset_accel_step :
    shape_vel_accel (10.0 * 1.0) 0.0 10.0 0.0 (-get_wp_acceleration_mss runParams.wpnav)
      (get_wp_acceleration_mss runParams.wpnav) (AC_PosControl.get_shaping_jerk_NE_msss runParams.psc)
      dtF true = 0.0 := by
  decide
/-- The zero target velocity has no direction. -/
theorem is_positive_zero_vec : is_positive ({} : Vector3f).length_squared = false := by decide
/-- Half the terrain margin. -/
theorem half_ten : ((0.5 : Float32) * 10.0) = 5.0 := by decide

/-! ## The empty leg -/

/-- The empty leg's clock does not move (its end time is zero). -/
theorem advance_time_init :
    SimplePath.advance_time SimplePath.init (1.0 * 1.0 * dtF) = SimplePath.init := by
  simp only [SimplePath.advance_time, SimplePath.init, SimplePath.time_end]
  congr 1

/-- The empty leg's profile is zero. -/
theorem accel_vel_pos_init :
    SimplePath.init.get_accel_vel_pos_at_time SimplePath.init.time = (0.0, 0.0, 0.0) := rfl

/-- Projecting onto the empty leg adds nothing. -/
theorem project_init (A V P : ftype) (pos : Vector3p) (vel accel : Vector3f) :
    SimplePath.init.project_onto_track A V P pos vel accel = (pos, vel, accel) := by
  simp only [SimplePath.project_onto_track]
  rw [if_pos (by decide)]

/-- `move_to_pos_vel_accel` on the empty leg subtracts its (zero) widened displacement. -/
theorem move_to_init (pos : Vector3p) (vel accel : Vector3f) :
    SimplePath.init.move_to_pos_vel_accel (1.0 * 1.0 * dtF) pos vel accel =
      (SimplePath.init, pos - ({} : Vector3f).topostype, vel, accel) := by
  simp only [SimplePath.move_to_pos_vel_accel, advance_time_init, accel_vel_pos_init, project_init]
  rfl

/-- `move_from_pos_vel_accel` on the empty leg adds nothing. -/
theorem move_from_init (pos : Vector3p) (vel accel : Vector3f) :
    SimplePath.init.move_from_pos_vel_accel (1.0 * 1.0 * dtF) pos vel accel =
      (SimplePath.init, pos, vel, accel) := by
  simp only [SimplePath.move_from_pos_vel_accel, advance_time_init, accel_vel_pos_init, project_init]

/-- The empty leg is finished. -/
theorem finished_init : SimplePath.init.finished = true := by decide
/-- The empty leg has not started. -/
theorem is_zero_elapsed_init : is_zero SimplePath.init.get_time_elapsed = true := by decide

/-- Three empty legs: the target is the origin minus the widened zero vector, with zero velocity
and acceleration, and the leg is finished. -/
theorem advance_target_init (r a : ftype) (pos : Vector3p) :
    SimplePath.init.advance_target_along_track SimplePath.init SimplePath.init r a false
        (1.0 * 1.0 * dtF) pos {} {} =
      ((SimplePath.init, SimplePath.init, SimplePath.init),
        (pos - ({} : Vector3f).topostype, {}, {}), true) := by
  simp only [SimplePath.advance_target_along_track, move_to_init, move_from_init, finished_init,
    is_zero_elapsed_init, Bool.false_and, Bool.not_true, Bool.false_eq_true, if_false]
  rfl

/-! ## The target sent to the position controller -/

/-- The position target. -/
def tp0 : Vector3p := hoverWP - ({} : Vector3f).topostype
/-- The velocity target. -/
def tv0 : Vector3f := ({} : Vector3f) * (1.0 : Float32)
/-- The acceleration target. -/
def ta0 : Vector3f := ({} : Vector3f) * AP_Math.sq (1.0 : Float32) + ({} : Vector3f)

/-- The north target is a binary64 zero. -/
theorem tp0_x (C : ConvZero) : ZD tp0.x :=
  ZD_sub ZD_zero (C.toFloat_zero 0 Z_zero)

/-- The east target is a binary64 zero. -/
theorem tp0_y (C : ConvZero) : ZD tp0.y :=
  ZD_sub ZD_zero (C.toFloat_zero 0 Z_zero)

/-- The down target has the exact value `-1`. -/
theorem tp0_z (C : ConvZero) : Near64 tp0.z (-1) 0 := by
  have hm : (-1 : Float).IsFinite := (Float.isFinite_neg 1).2 Float.isFinite_one
  have hz := C.toFloat_zero 0 Z_zero
  obtain ⟨hf, hv⟩ := sub_exact_d (f := -1) hm hz.1 hm (by rw [hz.2, sub_zero])
  refine ⟨hf, ?_⟩
  rw [show tp0.z = (-1 : Float) - Float32.toFloat 0 from rfl, hv, Float.toReal_neg, Float.toReal_one]
  simp

/-- The velocity target is a zero vector. -/
theorem tv0_zero : ZV tv0 := ZV_mul ZV_zero_lit lit_one.1

/-- The acceleration target is a zero vector. -/
theorem ta0_zero : ZV ta0 := ZV_add (ZV_mul ZV_zero_lit (One_sq lit_one).1) ZV_zero_lit

/-! ## The reads of the position controller -/

/-- Frame lemma: setting the terrain target keeps the desired velocity. -/
theorem vel_desired_frame (psc : AC_PosControl.State) (t : ftype) :
    AC_PosControl.get_vel_desired_NED_ms (AC_PosControl.set_pos_terrain_target_D_m psc t) =
      psc._vel_desired_ned_ms := rfl
/-- Frame lemma: setting the terrain target keeps the velocity offset. -/
theorem vel_offset_frame (psc : AC_PosControl.State) (t : ftype) :
    AC_PosControl.get_vel_offset_D_ms (AC_PosControl.set_pos_terrain_target_D_m psc t) =
      psc._vel_offset_ned_ms.z := rfl
/-- Frame lemma: setting the terrain target keeps the position estimate. -/
theorem pos_estimate_frame (psc : AC_PosControl.State) (t : ftype) :
    AC_PosControl.get_pos_estimate_NED_m (AC_PosControl.set_pos_terrain_target_D_m psc t) =
      psc._pos_estimate_ned_m := rfl
/-- Frame lemma: setting the terrain target keeps the position offset. -/
theorem pos_offset_frame (psc : AC_PosControl.State) (t : ftype) :
    AC_PosControl.get_pos_offset_NED_m (AC_PosControl.set_pos_terrain_target_D_m psc t) =
      psc._pos_offset_ned_m := rfl

/-- The desired velocity minus the vertical offset is a zero vector, so the track-error branch of
`advance_wp_target_along_track` is skipped. -/
theorem is_positive_vel_zero {psc : AC_PosControl.State} (hvd : ZV psc._vel_desired_ned_ms)
    (hvo : CopterZero.Z psc._vel_offset_ned_ms.z) :
    is_positive (Vector3f.mk psc._vel_desired_ned_ms.x psc._vel_desired_ned_ms.y
      (psc._vel_desired_ned_ms.z - psc._vel_offset_ned_ms.z)).length_squared = false := by
  obtain ⟨hx, hy, hz⟩ := hvd
  have hz' := Z_sub hz hvo
  exact is_positive_Z (Z_add (Z_add (Z_mul_left hx hx.1) (Z_mul_left hy hy.1)) (Z_mul_left hz' hz'.1))

/-- `constrain_float` of a finite value above `hi` (and not below `lo`) returns `hi` itself. -/
theorem constrain_float_of_gt {x lo hi : Float32} (hx : x.IsFinite) (hlo : lo.IsFinite)
    (hhi : hi.IsFinite) (h1 : lo.toReal ≤ x.toReal) (h2 : hi.toReal < x.toReal) :
    constrain_float x lo hi = hi := by
  show Contracts.Float32Clip.constrain_float x lo hi = hi
  unfold Contracts.Float32Clip.constrain_float
  rw [if_neg (Contracts.Float32Clip.not_isNaN_of_isFinite hx), if_neg (not_lt_of hx hlo h1),
    if_pos (lt_true hhi hx h2)]

/-- **The terrain scaler at the hover is the literal `1.0`.** The altitude error, estimate minus
target (with a zero terrain offset), is within `1/50` of zero in binary64, within `1/25` after
narrowing, so `1 - (|err| - 5) / 5` is near `2`, above the upper clip bound `1`. -/
theorem terrain_scaler_one (C : ConvZero) (N : NarrowSpec 2) {psc : AC_PosControl.State}
    (hter : CopterZero.Z psc._pos_terrain_d_m)
    (hpe : Near64 psc._pos_estimate_ned_m.z (-1) (1/100))
    (hpt : Near64 psc._pos_target_ned_m.z (-1) (1/100)) :
    AC_PosControl.terrain_scaler_D_m psc 0.0 (get_terrain_margin_m runParams.wpnav) = 1.0 := by
  rw [terrain_margin_eq]
  unfold AC_PosControl.terrain_scaler_D_m
  simp only [is_zero_ten, Bool.false_eq_true, if_false, half_ten]
  -- the binary64 error
  have hz : ZD (topostype ((0.0 : Float32) - psc._pos_terrain_d_m)) :=
    C.toFloat_zero _ (Z_sub Z_lit0 hter)
  have h1 : Near64 (psc._pos_target_ned_m.z + topostype ((0.0 : Float32) - psc._pos_terrain_d_m))
      (-1) (1/100) := by
    obtain ⟨hf, hv⟩ := add_ZD_right hpt.1 hz
    exact ⟨hf, by rw [hv]; exact hpt.2⟩
  have h2 := near64_sub (B := 1/50) hpe h1 (by norm_num) (by norm_num)
  have h2' : Near64 (psc._pos_estimate_ned_m.z - (psc._pos_target_ned_m.z +
      topostype ((0.0 : Float32) - psc._pos_terrain_d_m))) 0 (3/100) := by
    refine ⟨h2.1, ?_⟩
    have h := h2.2
    have he : (2 : ℝ) ^ (-53 : ℤ) ≤ 1 := zpow_le_one_of_nonpos₀ one_le_two (by norm_num)
    rw [show ((-1 : ℝ) - -1) = 0 by norm_num] at h
    nlinarith
  -- narrowing
  have h3 := near_narrow N h2' (by norm_num)
  set x := tofloat (psc._pos_estimate_ned_m.z - (psc._pos_target_ned_m.z +
      topostype ((0.0 : Float32) - psc._pos_terrain_d_m))) with hxdef
  have hx : Near32 x 0 (1/25) := by
    refine ⟨h3.1, h3.2.trans ?_⟩
    have := u32_le; have := η32_le; have := u32_nonneg
    norm_num
    nlinarith
  -- `|x|`
  have hxa : Near32 x.abs 0 (1/25) := by
    refine ⟨abs_isFinite hx.1, ?_⟩
    rw [abs_val, sub_zero, abs_abs]
    have := hx.2; rwa [sub_zero] at this
  -- the literal `5`
  have h5 : Near32 (5.0 : Float32) 5 0 := by
    obtain ⟨hf, hv⟩ := lit32 (x := (5.0 : Float32)) 10485760 (-21) (by decide) rfl
    exact ⟨hf, by rw [hv]; norm_num⟩
  -- `|x| - 5`
  have hd := near_sub (B := 6) hxa h5 (by norm_num) (by norm_num)
  have hd' : Near32 (x.abs - 5.0) (-5) (1/20) := by
    refine ⟨hd.1, ?_⟩
    have h := hd.2
    have := u32_le
    rw [show ((0 : ℝ) - 5) = -5 by norm_num] at h
    linarith
  -- `(|x| - 5) / 5`
  have hq := near_div (Ra := 5) hd' h5 (by norm_num) (by norm_num) (by norm_num)
  have hq' : Near32 ((x.abs - 5.0) / 5.0) (-1) (1/50) := by
    refine ⟨hq.1, ?_⟩
    have h := hq.2
    have := u32_le; have := η32_le; have := u32_nonneg
    norm_num at h ⊢
    linarith
  -- `1 - (|x| - 5) / 5`
  have hy := near_sub (B := 3) (CopterVertNear.One_lit1.near) hq' (by norm_num) (by norm_num)
  have hlo := lit32 (x := (0.01 : Float32)) 10737418 (-30) (by decide) rfl
  have hhi := CopterVertNear.One_lit1
  apply constrain_float_of_gt hy.1 hlo.1 hhi.1
  · have h := hy.lo
    have := u32_le
    rw [hlo.2]
    norm_num at h ⊢
    linarith
  · have h := hy.lo
    have := u32_le
    rw [hhi.2]
    norm_num at h ⊢
    linarith

/-! ## One step of the navigator -/

/-- **`advance_wp_target_along_track` at the steady state.** The navigator state stays steady and
the position controller receives `(tp0, tv0, ta0)` after the terrain target is set to `0`. -/
theorem advance_steady (C : ConvZero) (N : NarrowSpec 2) {s : AC_WPNav.State} (hs : NavSteady s)
    {psc : AC_PosControl.State} (hvd : ZV psc._vel_desired_ned_ms)
    (hvo : CopterZero.Z psc._vel_offset_ned_ms.z) (hter : CopterZero.Z psc._pos_terrain_d_m)
    (hpe : Near64 psc._pos_estimate_ned_m.z (-1) (1/100))
    (hpt : Near64 psc._pos_target_ned_m.z (-1) (1/100)) :
    ∃ s' : AC_WPNav.State, NavSteady s' ∧
      advance_wp_target_along_track runParams.wpnav runParams.psc s psc dtF =
        (s', AC_PosControl.set_pos_vel_accel_NED_m (AC_PosControl.set_pos_terrain_target_D_m psc 0.0)
          tp0 tv0 ta0, true) := by
  have hsc := terrain_scaler_one C N hter hpe hpt
  have hpos := is_positive_vel_zero hvd hvo
  obtain ⟨a1, a2, a3, ⟨f1, f2⟩, a5, a6, a7, a8, l1, l2, l3, b1, b2, b3, b4, b5, b6, b7, b8, b9,
    b10, b11, b12⟩ := s
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl⟩ := hs
  simp only [advance_wp_target_along_track, hsc, vel_desired_frame, vel_offset_frame,
    pos_estimate_frame, pos_offset_frame, advance_target_init, hpos, is_positive_ten,
    is_zero_lit_one, offset_vel_step, ten_div_ten, track_dt_step, offset_accel_step,
    is_positive_zero_vec, Bool.not_false, Bool.false_eq_true, if_true, if_false]
  split_ifs <;> exact ⟨_, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl⟩, rfl⟩

/-- `update_wpnav` at the steady state: the speed-change checks are skipped, so it is
`advance_wp_target_along_track` with PosControl's `dt`, the horizontal controller and the time
stamp. -/
theorem update_wpnav_eq {s : AC_WPNav.State} (hs : NavSteady s) (psc : AC_PosControl.State)
    (env : AC_WPNav.Env) :
    AC_WPNav.update_wpnav runParams.wpnav runParams.psc s psc env =
      ({ (advance_wp_target_along_track runParams.wpnav runParams.psc s psc
            (AC_PosControl.get_dt_s psc)).1 with _wp_last_update_ms := env.clock.millis },
        AC_PosControl.NE_update_controller runParams.psc
          (advance_wp_target_along_track runParams.wpnav runParams.psc s psc
            (AC_PosControl.get_dt_s psc)).2.1 env.ahrs env.att env.clock,
        (advance_wp_target_along_track runParams.wpnav runParams.psc s psc
          (AC_PosControl.get_dt_s psc)).2.2) := by
  simp only [update_wpnav, hs.check_speed, hs.wp_speed, hs.last_speed, hs.last_speed_up,
    hs.last_speed_down, is_equal_ten, is_equal_spd_up, is_equal_spd_dn, Bool.not_true,
    Bool.false_eq_true, if_true, if_false]
  rfl

/-- **The navigator at the hover.** From the steady state, `update_wpnav` with the run parameters
returns a steady state and sends the position controller the target `(±0, ±0, -1)` with zero
velocity and acceleration, then runs `NE_update_controller`. -/
theorem update_wpnav_steady (C : ConvZero) (N : NarrowSpec 2) {s : AC_WPNav.State}
    (hs : NavSteady s) {psc : AC_PosControl.State} (env : AC_WPNav.Env)
    (hdt : psc._dt_s = dtF)
    (hvd : ZV psc._vel_desired_ned_ms) (hvo : CopterZero.Z psc._vel_offset_ned_ms.z)
    (hter : CopterZero.Z psc._pos_terrain_d_m)
    (hpe : Near64 psc._pos_estimate_ned_m.z (-1) (1/100))
    (hpt : Near64 psc._pos_target_ned_m.z (-1) (1/100)) :
    ∃ s' : AC_WPNav.State, ∃ tp : Vector3p, ∃ tv ta : Vector3f,
      NavSteady s' ∧ ZD tp.x ∧ ZD tp.y ∧ Near64 tp.z (-1) 0 ∧ ZV tv ∧ ZV ta ∧
      AC_WPNav.update_wpnav runParams.wpnav runParams.psc s psc env =
        (s', AC_PosControl.NE_update_controller runParams.psc
          (AC_PosControl.set_pos_vel_accel_NED_m (AC_PosControl.set_pos_terrain_target_D_m psc 0.0)
            tp tv ta) env.ahrs env.att env.clock, true) := by
  obtain ⟨s', hs', hA⟩ := advance_steady C N hs hvd hvo hter hpe hpt
  refine ⟨{ s' with _wp_last_update_ms := env.clock.millis }, tp0, tv0, ta0,
    hs'.with_last_update _, tp0_x C, tp0_y C, tp0_z C, tv0_zero, ta0_zero, ?_⟩
  rw [update_wpnav_eq hs, show AC_PosControl.get_dt_s psc = dtF from hdt, hA]

end Contracts.CopterHover
