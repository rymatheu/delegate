import Contracts.CopterHoverTick0Init

/-!
# Tick 0 of the hover run: the mission start

After the switch into Auto, `ModeAuto::run` finds `waiting_to_start` set and starts the mission
(`mission_start`): the mission is running, `advance_current_nav_cmd` loads its only command
`hoverCmd` and starts it (`start_command`, `do_nav_wp`, `wp_start`). The navigator is active
(its stamp is the current `millis() = 2`) and its destination was reached at the
initialization, so `set_wp_destination_NED_m` does not re-initialize: the origin becomes the
previous destination, the stopping point of the boot controller, the destination the waypoint
`hoverWP`, and the leg between them is the empty leg, its squared length being below the
`is_zero` threshold (`t0_leg_is_zero`). AutoYaw stays in its default `LOOK_AT_NEXT_WP`, the submode
becomes `WP`, the loiter fields are zero, and `set_next_wp` finds no command after `hoverCmd`.
`run` then clears `waiting_to_start` and dispatches to `wp_run` (`t0_run_eq`).
-/

namespace Contracts.CopterHover

open AP_Math AC_WPNav Contracts.CopterZero
open Contracts.CopterVertNear (Near32 Near64 NarrowSpec near_narrow u32_le η32_le u32_nonneg
  η32_nonneg)

/-- A leg from a stopping point within `2 · 10⁻⁵` of the waypoint to the waypoint has a squared
length below the `is_zero` threshold of `calculate_track` (the reverse of `leg_is_zero`). -/
theorem t0_leg_is_zero (C : ConvZero) (N : NarrowSpec 2) {SP : Vector3p} (hx : ZD SP.x)
    (hy : ZD SP.y) (hz : Near64 SP.z (-1) (2 / 100000)) :
    is_zero (hoverWP - SP).tofloat.length_squared = true := by
  have hu := u32_le; have hu0 := u32_nonneg; have hη := η32_le; have hη0 := η32_nonneg
  have dx : CopterZero.Z (tofloat (hoverWP.x - SP.x)) := C.toFloat32_zero _ (ZD_sub ZD_zero hx)
  have dy : CopterZero.Z (tofloat (hoverWP.y - SP.y)) := C.toFloat32_zero _ (ZD_sub ZD_zero hy)
  have h1 := Contracts.CopterVertNear.near64_sub (B := 2) hoverWP_z_near hz (by norm_num)
    (by norm_num)
  have h2 := near_narrow N h1 (by norm_num)
  have h2' : Near32 (tofloat (hoverWP.z - SP.z)) 0 (3 / 100000) := by
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
  show is_zero (tofloat (hoverWP.x - SP.x) * tofloat (hoverWP.x - SP.x) +
    tofloat (hoverWP.y - SP.y) * tofloat (hoverWP.y - SP.y) +
    tofloat (hoverWP.z - SP.z) * tofloat (hoverWP.z - SP.z)) = true
  apply Contracts.CopterVertNear.is_zero_true hsum.1
  have := hsum.2
  rw [mul_zero, sub_zero] at this
  refine lt_of_le_of_lt this ?_
  norm_num
  nlinarith

/-- **`set_wp_destination_NED_m` from the navigator of the initialization.** The navigator is
active and its destination reached, so there is no re-initialization; the origin becomes the
previous destination, the destination `hoverWP`, the leg the empty leg, the flags are cleared,
and the position controller is unchanged. -/
theorem t0_set_dest (W0 : AC_WPNav.State) (psc : AC_PosControl.State) (env : AC_WPNav.Env)
    (hact : AC_WPNav.is_active W0 env.clock = true)
    (hr : W0._flags = { reached_destination := true, fast_waypoint := false })
    (hthis : W0._path_this_leg = SimplePath.init)
    (hleg : SimplePath.calculate_track W0._destination_ned_m hoverWP
      (AC_PosControl.NE_get_max_speed_ms psc) (AC_PosControl.get_max_speed_up_ms psc)
      (AC_PosControl.get_max_speed_down_ms psc) (get_wp_acceleration_mss runParams.wpnav)
      (get_accel_D_mss runParams.wpnav) = SimplePath.init) :
    set_wp_destination_NED_m runParams.wpnav runParams.psc W0 psc env hoverWP =
      ({ W0 with
        _path_prev_leg := SimplePath.init
        _origin_ned_m := W0._destination_ned_m
        _destination_ned_m := hoverWP
        _is_terrain_alt := false
        _path_this_leg := SimplePath.init
        _path_next_leg := SimplePath.init
        _next_destination_ned_m := W0._next_destination_ned_m.zero
        _flags := { reached_destination := false, fast_waypoint := false } }, psc) := by
  unfold set_wp_destination_NED_m
  simp only [Id.run, hact, hr, hthis, hleg, Bool.not_true, Bool.or_false, Bool.false_and,
    Bool.false_eq_true, if_false]
  rfl

/-- The default AutoYaw mode of the run (`WP_YAW_BEHAVIOR = 2`, not RTL) is `LOOK_AT_NEXT_WP`. -/
theorem t0_default_yaw : Copter.AutoYaw.default_mode runParams false = .LOOK_AT_NEXT_WP := by
  decide

/-- `wp_start` on an active navigator with AutoYaw already in its default mode: the destination
is set, AutoYaw is unchanged, and the submode becomes `WP`. -/
theorem t0_wp_start_eq (t : Copter.State) (hact : AC_WPNav.is_active t.wp_nav t.clock = true)
    (hyaw : t.auto_yaw._mode = .LOOK_AT_NEXT_WP) :
    Copter.ModeAuto.wp_start runParams t hoverCmd.location = { t with
      wp_nav := (set_wp_destination_NED_m runParams.wpnav runParams.psc t.wp_nav t.pos_control
        (t.wpEnv runParams) hoverWP).1
      pos_control := (set_wp_destination_NED_m runParams.wpnav runParams.psc t.wp_nav
        t.pos_control (t.wpEnv runParams) hoverWP).2
      mode_auto := { t.mode_auto with _mode := .WP } } := by
  have hdef : (t.auto_yaw._mode == Copter.AutoYaw.default_mode runParams false) = true := by
    rw [hyaw, t0_default_yaw]; rfl
  unfold Copter.ModeAuto.wp_start
  simp only [Id.run, hact, Bool.not_true, Bool.false_eq_true, if_false]
  unfold Copter.AutoYaw.set_mode_to_default Copter.AutoYaw.set_mode Copter.ModeAuto.set_submode
  simp only [hdef, if_true]
  rfl

/-- `set_next_wp` after `hoverCmd`: the hover mission has no further command. -/
theorem t0_set_next_wp (t : Copter.State) :
    Copter.ModeAuto.set_next_wp runParams t hoverCmd = t := by
  unfold Copter.ModeAuto.set_next_wp
  rw [if_neg (by decide)]
  rfl

/-- `mission_start` on the hover mission: the mission runs with `hoverCmd` loaded, and the
command is started. -/
theorem t0_mission_start_eq (s : Copter.State) :
    Copter.ModeAuto.mission_start runParams s = Copter.ModeAuto.start_command runParams
      { s with mode_auto := { s.mode_auto with
        mission := (⟨.MISSION_RUNNING, some hoverCmd, true⟩ : Copter.Mission) } } hoverCmd := rfl

/-- **`ModeAuto::run` at tick 0.** With `waiting_to_start` set, the navigator active and AutoYaw
in `LOOK_AT_NEXT_WP`: the mission starts with `hoverCmd`, the navigator gets its destination
`hoverWP` from `set_wp_destination_NED_m`, the submode becomes `WP`, the loiter fields zero, and
`run` is `wp_run` on that state. -/
theorem t0_run_eq (s : Copter.State) (hw : s.mode_auto.waiting_to_start = true)
    (hact : AC_WPNav.is_active s.wp_nav s.clock = true)
    (hyaw : s.auto_yaw._mode = .LOOK_AT_NEXT_WP) :
    Copter.ModeAuto.run runParams s = Copter.ModeAuto.wp_run runParams { s with
      wp_nav := (set_wp_destination_NED_m runParams.wpnav runParams.psc s.wp_nav s.pos_control
        (s.wpEnv runParams) hoverWP).1
      pos_control := (set_wp_destination_NED_m runParams.wpnav runParams.psc s.wp_nav
        s.pos_control (s.wpEnv runParams) hoverWP).2
      mode_auto := { s.mode_auto with
        _mode := .WP, waiting_to_start := false, loiter_time := 0, loiter_time_max := 0,
        mission := (⟨.MISSION_RUNNING, some hoverCmd, true⟩ : Copter.Mission) } } := by
  have h1 : Copter.ModeAuto.mission_start runParams s = { s with
      wp_nav := (set_wp_destination_NED_m runParams.wpnav runParams.psc s.wp_nav s.pos_control
        (s.wpEnv runParams) hoverWP).1
      pos_control := (set_wp_destination_NED_m runParams.wpnav runParams.psc s.wp_nav
        s.pos_control (s.wpEnv runParams) hoverWP).2
      mode_auto := { s.mode_auto with
        _mode := .WP, loiter_time := 0, loiter_time_max := 0,
        mission := (⟨.MISSION_RUNNING, some hoverCmd, true⟩ : Copter.Mission) } } := by
    rw [t0_mission_start_eq]
    unfold Copter.ModeAuto.start_command Copter.ModeAuto.do_nav_wp
    rw [t0_set_next_wp, t0_wp_start_eq]
    · rfl
    · exact hact
    · exact hyaw
  unfold Copter.ModeAuto.run
  simp only [Id.run, hw, if_true, h1]
  rfl

end Contracts.CopterHover
