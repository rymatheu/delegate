import Contracts.CopterHoverTick0Start

/-!
# Tick 0 of the hover run: the first `update_wpnav`

The first `wp_run` of the run calls `update_wpnav` on the navigator left by the mission start:
the steady form of `Contracts.CopterHover.NavSteady` except that the leg origin is the boot
stopping point `o` (a binary64 position within `10⁻⁶` of the waypoint, zero horizontally) and
the destination `hoverWP` is not yet reached. `t0_update_wpnav` is the analogue of
`update_wpnav_steady`:

* the speed bookkeeping, the offset velocity and the track time scalar stay at their steady
  values (the same kernel computations as in `advance_steady`);
* the target sent to the position controller is the origin minus the widened zero vector, so its
  horizontal components are binary64 zeros (`ConvZero`) and its altitude has the value of the
  origin's, with zero velocity and acceleration;
* the leg is the empty leg, which is finished, the waypoint is not a fast waypoint, and the
  vehicle is within the waypoint radius `2 m` of the destination (`t0_reach_le`: the squared
  distance, formed in binary64 and narrowed, is a few `10⁻³⁰`), so `reached_destination` is set.
-/

namespace Contracts.CopterHover

open AP_Math AC_WPNav Contracts.CopterZero
open Contracts.CopterVertNear (Near32 Near64 NarrowSpec dtF near_narrow u32_le η32_le u32_nonneg
  η32_nonneg)

/-- `sq 2.0 = 4.0` in binary32, and the value of `4.0`. -/
theorem t0_sq_two : AP_Math.sq (2.0 : Float32) = 4.0 ∧ (4.0 : Float32).IsFinite ∧
    (4.0 : Float32).toReal = 4 := by
  obtain ⟨h1, h2⟩ := Contracts.CopterVertNear.lit32 (x := (4.0 : Float32)) 8388608 (-21)
    (by decide) rfl
  exact ⟨by decide, h1, by rw [h2]; norm_num⟩

/-- **The reached-destination check at tick 0**: a binary64 position with zero horizontal
components and an altitude within `10⁻¹⁴` of `-1` is within the waypoint radius `2` of
`hoverWP` (squared distance narrowed to binary32, compared with `sq 2.0`). -/
theorem t0_reach_le (C : ConvZero) (N : NarrowSpec 2) {c : Vector3p} (hx : ZD c.x) (hy : ZD c.y)
    (hz : Near64 c.z (-1) 1e-14) :
    (c - hoverWP).tofloat.length_squared ≤ AP_Math.sq (2.0 : Float32) := by
  have hu := u32_le; have hu0 := u32_nonneg; have hη := η32_le; have hη0 := η32_nonneg
  have dx : CopterZero.Z (tofloat (c.x - hoverWP.x)) := C.toFloat32_zero _ (ZD_sub hx ZD_zero)
  have dy : CopterZero.Z (tofloat (c.y - hoverWP.y)) := C.toFloat32_zero _ (ZD_sub hy ZD_zero)
  have h1 := Contracts.CopterVertNear.near64_sub (B := 2) hz hoverWP_z_near (by norm_num)
    (by norm_num)
  have h2 := near_narrow N h1 (by norm_num)
  have h2' : Near32 (tofloat (c.z - hoverWP.z)) 0 (1 / 1000) := by
    refine ⟨h2.1, ?_⟩
    have := h2.2
    have he : (2 : ℝ) ^ (-53 : ℤ) ≤ 1 := zpow_le_one_of_nonpos₀ one_le_two (by norm_num)
    have he0 : (0 : ℝ) ≤ 2 ^ (-53 : ℤ) := (zpow_pos two_pos _).le
    rw [show (-1 : ℝ) - -1 = 0 by norm_num] at this
    refine this.trans ?_
    norm_num
    nlinarith
  have h3 := Contracts.CopterVertNear.near_mul h2' h2' (Ra := 0) (Rb := 0) (by simp) (by simp)
    (by norm_num)
  have hxy := Z_add (Z_mul_left dx dx.1) (Z_mul_left dy dy.1)
  have hsum := Near32.zero_add h3 ⟨hxy.1, hxy.2⟩
  obtain ⟨q1, q2, q3⟩ := t0_sq_two
  show tofloat (c.x - hoverWP.x) * tofloat (c.x - hoverWP.x) +
    tofloat (c.y - hoverWP.y) * tofloat (c.y - hoverWP.y) +
    tofloat (c.z - hoverWP.z) * tofloat (c.z - hoverWP.z) ≤ AP_Math.sq (2.0 : Float32)
  rw [q1, le_iff hsum.1 q2, q3]
  have := hsum.2
  rw [mul_zero, sub_zero] at this
  have := (abs_le.1 this).2
  have : (0 + 1 / 1000) * (1 / 1000) + 0 * 0 + Contracts.CopterVertNear.u32 *
      ((0 + 1 / 1000) * (0 + 1 / 1000)) + Contracts.CopterVertNear.η32 ≤ (4 : ℝ) := by
    norm_num; nlinarith
  linarith

/-- **`advance_wp_target_along_track` at tick 0.** From the steady navigator with origin `o`,
destination `hoverWP` not yet reached: the navigator stays steady (with origin `o`), the
destination is reached, and the position controller receives the origin minus the widened zero
vector, zero velocity and acceleration, after the terrain target is set to `0`. -/
theorem t0_advance (C : ConvZero) (N : NarrowSpec 2) {s : AC_WPNav.State}
    (hs : NavSteady { s with _origin_ned_m := hoverWP }) (hd : s._destination_ned_m = hoverWP)
    (hr : s._flags.reached_destination = false)
    {psc : AC_PosControl.State} (hvd : ZV psc._vel_desired_ned_ms)
    (hvo : CopterZero.Z psc._vel_offset_ned_ms.z) (hter : CopterZero.Z psc._pos_terrain_d_m)
    (hpe : Near64 psc._pos_estimate_ned_m.z (-1) 1e-15)
    (hpex : ZD psc._pos_estimate_ned_m.x) (hpey : ZD psc._pos_estimate_ned_m.y)
    (hpo : ZD psc._pos_offset_ned_m.x ∧ ZD psc._pos_offset_ned_m.y ∧ ZD psc._pos_offset_ned_m.z)
    (hpt : Near64 psc._pos_target_ned_m.z (-1) (1/100)) :
    ∃ s' : AC_WPNav.State, NavSteady { s' with _origin_ned_m := hoverWP } ∧
      s'._origin_ned_m = s._origin_ned_m ∧ s'._destination_ned_m = hoverWP ∧
      s'._flags.reached_destination = true ∧
      advance_wp_target_along_track runParams.wpnav runParams.psc s psc dtF =
        (s', AC_PosControl.set_pos_vel_accel_NED_m
          (AC_PosControl.set_pos_terrain_target_D_m psc 0.0)
          (s._origin_ned_m - ({} : Vector3f).topostype) tv0 ta0, true) := by
  have hpe' : Near64 psc._pos_estimate_ned_m.z (-1) (1/100) := ⟨hpe.1, hpe.2.trans (by norm_num)⟩
  have hsc := terrain_scaler_one C N hter hpe' hpt
  have hpos := is_positive_vel_zero hvd hvo
  -- the reached-destination check
  have hc0 : ZD (topostype (0.0 : Float32)) := C.toFloat_zero _ Z_lit0
  obtain ⟨ex1, ex2⟩ := sub_ZD_right hpex.1 hpo.1
  obtain ⟨ey1, ey2⟩ := sub_ZD_right hpey.1 hpo.2.1
  obtain ⟨ez1, ez2⟩ := sub_ZD_right hpe.1 hpo.2.2
  obtain ⟨ez3, ez4⟩ := sub_ZD_right ez1 hc0
  have hreach := t0_reach_le C N
    (c := { (psc._pos_estimate_ned_m - psc._pos_offset_ned_m) with
      z := (psc._pos_estimate_ned_m - psc._pos_offset_ned_m).z - topostype (0.0 : Float32) })
    ⟨ex1, ex2.trans hpex.2⟩ ⟨ey1, ey2.trans hpey.2⟩
    ⟨ez3, by
      show |(psc._pos_estimate_ned_m.z - psc._pos_offset_ned_m.z -
        topostype (0.0 : Float32)).toReal - -1| ≤ 1e-14
      rw [ez4, ez2]; exact hpe.2.trans (by norm_num)⟩
  obtain ⟨a1, a2, a3, ⟨f1, f2⟩, a5, a6, a7, a8, l1, l2, l3, b1, b2, b3, b4, b5, b6, b7, b8, b9,
    b10, b11, b12⟩ := s
  simp only at hd hr
  subst hd hr
  obtain ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, -, rfl, rfl, rfl, rfl,
    rfl⟩ := hs
  simp only [advance_wp_target_along_track, hsc, vel_desired_frame, vel_offset_frame,
    pos_estimate_frame, pos_offset_frame, advance_target_init, hpos, is_positive_ten,
    is_zero_lit_one, offset_vel_step, ten_div_ten, track_dt_step, offset_accel_step,
    is_positive_zero_vec, Bool.not_false, Bool.false_eq_true, if_true, if_false, hreach]
  exact ⟨_, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl⟩, rfl, rfl, rfl, rfl⟩

/-- **The navigator at tick 0.** From the steady navigator with origin `o` (zero horizontally,
within `10⁻⁶` of `-1` vertically) and destination `hoverWP` not yet reached, `update_wpnav`
returns a navigator that is steady with origin `o`, has reached `hoverWP`, and carries the time
stamp of the clock, and sends the position controller a target with zero horizontal components
and an altitude within `10⁻⁶` of `-1`, with zero velocity and acceleration, then runs
`NE_update_controller`. -/
theorem t0_update_wpnav (C : ConvZero) (N : NarrowSpec 2) {s : AC_WPNav.State}
    (hs : NavSteady { s with _origin_ned_m := hoverWP }) (hox : ZD s._origin_ned_m.x)
    (hoy : ZD s._origin_ned_m.y) (hoz : Near64 s._origin_ned_m.z (-1) 1e-6)
    (hd : s._destination_ned_m = hoverWP) (hr : s._flags.reached_destination = false)
    {psc : AC_PosControl.State} (env : AC_WPNav.Env) (hdt : psc._dt_s = dtF)
    (hvd : ZV psc._vel_desired_ned_ms)
    (hvo : CopterZero.Z psc._vel_offset_ned_ms.z) (hter : CopterZero.Z psc._pos_terrain_d_m)
    (hpe : Near64 psc._pos_estimate_ned_m.z (-1) 1e-15)
    (hpex : ZD psc._pos_estimate_ned_m.x) (hpey : ZD psc._pos_estimate_ned_m.y)
    (hpo : ZD psc._pos_offset_ned_m.x ∧ ZD psc._pos_offset_ned_m.y ∧ ZD psc._pos_offset_ned_m.z)
    (hpt : Near64 psc._pos_target_ned_m.z (-1) (1/100)) :
    ∃ s' : AC_WPNav.State, ∃ tp : Vector3p, ∃ tv ta : Vector3f,
      NavSteady { s' with _origin_ned_m := hoverWP } ∧ s'._origin_ned_m = s._origin_ned_m ∧
      s'._destination_ned_m = hoverWP ∧ s'._flags.reached_destination = true ∧
      s'._wp_last_update_ms = env.clock.millis ∧
      ZD tp.x ∧ ZD tp.y ∧ Near64 tp.z (-1) 1e-6 ∧ ZV tv ∧ ZV ta ∧
      AC_WPNav.update_wpnav runParams.wpnav runParams.psc s psc env =
        (s', AC_PosControl.NE_update_controller runParams.psc
          (AC_PosControl.set_pos_vel_accel_NED_m (AC_PosControl.set_pos_terrain_target_D_m psc 0.0)
            tp tv ta) env.ahrs env.att env.clock, true) := by
  obtain ⟨s', hs', ho', hd', hr', hA⟩ := t0_advance C N hs hd hr hvd hvo hter hpe hpex hpey hpo hpt
  have hz0 : ZD (Float32.toFloat 0) := C.toFloat_zero 0 Z_zero
  obtain ⟨tz1, tz2⟩ := sub_ZD_right hoz.1 hz0
  refine ⟨{ s' with _wp_last_update_ms := env.clock.millis },
    s._origin_ned_m - ({} : Vector3f).topostype, tv0, ta0, hs'.with_last_update _, ho', hd', hr',
    rfl, ZD_sub hox hz0, ZD_sub hoy hz0,
    ⟨tz1, by
      show |(s._origin_ned_m.z - Float32.toFloat 0).toReal - -1| ≤ 1e-6
      rw [tz2]; exact hoz.2⟩, tv0_zero, ta0_zero, ?_⟩
  have h1 : s._check_wp_speed_change = true := hs.check_speed
  have h2 : s._wp_speed_ms = 10.0 := hs.wp_speed
  have h3 : s._last_wp_speed_ms = 10.0 := hs.last_speed
  have h4 : s._last_wp_speed_up_ms = 2.5 := hs.last_speed_up
  have h5 : s._last_wp_speed_down_ms = 1.5 := hs.last_speed_down
  simp only [update_wpnav, h1, h2, h3, h4, h5, is_equal_ten, is_equal_spd_up, is_equal_spd_dn,
    Bool.not_true, Bool.false_eq_true, if_true, if_false]
  rw [show AC_PosControl.get_dt_s psc = dtF from hdt, hA]
  rfl

end Contracts.CopterHover
