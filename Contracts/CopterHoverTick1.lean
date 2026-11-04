import Contracts.CopterHoverPhase

/-!
# Tick 1 of the hover run: the mission completes and the vehicle loiters

The second tick of the closed-loop hover run takes the invariant `InvP1` (the state after tick 0)
to the steady invariant `InvSteady` of `Contracts.CopterHover`, from which `tick_steady` carries the
run on. The path through the code:

* the common prefix of the tick (`prefix_run`, which needs only `InvCore`) leaves the navigator, the
  Auto mode state, AutoYaw and the Auto flag alone and advances the clock to `micros = 5000`, so
  `millis() = 5` (`prefix_scheduler`); the vertical acceleration limit of the position controller
  is also kept (`prefix_accel_max`);
* `ModeAuto.run` calls `mission_update`, which verifies the loaded waypoint command: the waypoint is
  reached and the loiter time is zero, so the command is done (`verify_nav_wp_done`); there is no
  command at index `2` (`advance_nav_cmd_none`), so the mission completes and `exit_mission` runs
  `loiter_start` (`mission_update_complete`, `loiter_start_eq`);
* `loiter_start` computes the stopping point of the position controller: horizontally the zero
  position estimate (the velocity estimate is zero, `stopping_point_NE_zero`), vertically the
  altitude estimate plus the stopping distance of the vertical speed, which is the speed itself
  (`stopping_distance_small`), within `2 · 10⁻⁵` of the waypoint (`stopping_point_D_near`, with
  the widening `WidenSpec` and the narrowing `NarrowSpec`);
* `set_wp_destination_NED_m` does not re-initialize (the navigator is active, `5 - 2 < 200`, and the
  destination was reached) and builds the leg from the waypoint to the stopping point, which is the
  empty leg because its squared length is below `FLT_EPSILON` (`leg_is_zero`,
  `calculate_track_empty`); the navigator is then `NavSteady` (`set_wp_destination_loiter`) and
  the position controller is untouched;
* AutoYaw goes to `HOLD`, the submode to `LOITER`, and `run` dispatches to `loiter_run = wp_run`,
  where `wp_run_steady` applies (`PreRun.frame`: the facts of the prefix survive).

**Hypothesis beyond `InvP1`.** The vertical stopping distance is `inv_sqrt_controller(v, 1, a)` with
`a` the position controller's `_accel_max_d_mss`, which `InvCore` leaves free (`PscLim` asks only
finiteness and an upper bound). For a positive `a` below the speed `|v|` the stopping distance is
`a / 2 + v² / (2 a)`, which is not small, and the leg would not be empty. `tick_one` therefore
assumes `1/100 ≤ a` (the run has `a = 1`, `WP_ACC_Z`, set by `wp_and_spline_init_m` at tick 0).
-/

namespace Contracts.CopterHover

open AP_Math AC_WPNav Contracts.CopterZero
open Contracts.CopterVertNear (Near32 Near64 NarrowSpec near_narrow near_add u32 η32 u32_le η32_le
  u32_nonneg η32_nonneg lit32 constrain_float_of_near)

/-- `verify_nav_wp` on a reached waypoint with zero loiter time: done, only the loiter timer may
change. -/
theorem verify_nav_wp_done (s : Copter.State) (hr : s.wp_nav._flags.reached_destination = true)
    (hmax : s.mode_auto.loiter_time_max = 0) :
    ∃ lt : UInt32, Copter.ModeAuto.verify_nav_wp s =
      ({ s with mode_auto := { s.mode_auto with loiter_time := lt } }, true) := by
  have h0 : ∀ x : UInt32, s.mode_auto.loiter_time_max.toUInt32 ≤ x := by
    intro x; rw [hmax]; exact UInt32.zero_le
  unfold Copter.ModeAuto.verify_nav_wp
  simp only [AC_WPNav.reached_wp_destination, hr, Bool.not_true, Bool.false_eq_true, if_false]
  split
  · exact ⟨s.millis, by rw [if_pos (h0 _)]⟩
  · exact ⟨s.mode_auto.loiter_time, by rw [if_pos (h0 _)]⟩

/-- The hover mission has no command after `hoverCmd`. -/
theorem advance_nav_cmd_none (s : Copter.State)
    (hrun : s.mode_auto.mission.state = .MISSION_RUNNING)
    (hcmd : s.mode_auto.mission.nav_cmd = some hoverCmd)
    (hl : s.mode_auto.mission.nav_cmd_loaded = false) :
    Copter.ModeAuto.advance_current_nav_cmd runParams s = none := by
  unfold Copter.ModeAuto.advance_current_nav_cmd
  simp only [hrun, hl, hcmd]
  rfl

/-- **`mission_update` at tick 1.** The waypoint command is done, the mission completes and
`loiter_start` runs on the state with a new Auto mode state (mission complete, `waiting_to_start`
kept). -/
theorem mission_update_complete (s : Copter.State)
    (hrun : s.mode_auto.mission.state = .MISSION_RUNNING)
    (hcmd : s.mode_auto.mission.nav_cmd = some hoverCmd)
    (hl : s.mode_auto.mission.nav_cmd_loaded = true)
    (hr : s.wp_nav._flags.reached_destination = true)
    (hmax : s.mode_auto.loiter_time_max = 0) :
    ∃ ma : Copter.ModeAutoState,
      Copter.ModeAuto.mission_update runParams s =
        Copter.ModeAuto.loiter_start runParams { s with mode_auto := ma } ∧
      ma.waiting_to_start = s.mode_auto.waiting_to_start ∧
      ma.mission.state = .MISSION_COMPLETE := by
  obtain ⟨lt, hv⟩ := verify_nav_wp_done s hr hmax
  unfold Copter.ModeAuto.mission_update
  have c1 : (Copter.MissionState.MISSION_RUNNING != Copter.MissionState.MISSION_RUNNING ||
      runParams.mission.isEmpty) = false := rfl
  have c2 : (!true || (some hoverCmd).isNone) = false := rfl
  simp only [hrun, hl, hcmd, hv, c1, c2, Bool.false_eq_true, if_false, if_true]
  rw [advance_nav_cmd_none]
  · exact ⟨_, rfl, rfl, rfl⟩
  all_goals rfl

/-- A leg whose squared length is below `FLT_EPSILON` is the empty leg. -/
theorem calculate_track_empty (o d : Vector3p) (a b c e f : ftype)
    (h : is_zero (d - o).tofloat.length_squared = true) :
    SimplePath.calculate_track o d a b c e f = SimplePath.init := by
  unfold SimplePath.calculate_track
  simp only [Id.run, h, Bool.or_true, if_true]
  rfl

/-- **`set_wp_destination_NED_m` from the navigator of `NavP1`.** The navigator is active and the
waypoint reached, so there is no re-initialization; with an empty leg to the new destination the
navigator is `NavSteady` (origin `hoverWP`, three empty legs) and the position controller is
unchanged. -/
theorem set_wp_destination_loiter {W0 : AC_WPNav.State} (hn : NavP1 W0) (psc : AC_PosControl.State)
    (env : AC_WPNav.Env) (hact : AC_WPNav.is_active W0 env.clock = true) (SP : Vector3p)
    (hleg : SimplePath.calculate_track hoverWP SP (AC_PosControl.NE_get_max_speed_ms psc)
      (AC_PosControl.get_max_speed_up_ms psc) (AC_PosControl.get_max_speed_down_ms psc)
      (get_wp_acceleration_mss runParams.wpnav) (get_accel_D_mss runParams.wpnav) =
        SimplePath.init) :
    NavSteady (set_wp_destination_NED_m runParams.wpnav runParams.psc W0 psc env SP).1 ∧
      (set_wp_destination_NED_m runParams.wpnav runParams.psc W0 psc env SP).2 = psc := by
  have hs := hn.steady
  have hf : W0._flags.fast_waypoint = false := hs.fast_waypoint
  have hthis : W0._path_this_leg = SimplePath.init := hs.this_leg
  unfold set_wp_destination_NED_m
  simp only [Id.run, hact, hn.reached, hn.dest, hf, hthis, hleg, Bool.not_true, Bool.or_false,
    Bool.false_and, Bool.false_eq_true, if_false]
  exact ⟨⟨hs.wp_speed, hs.wp_radius, hs.wp_jerk, rfl, hs.check_speed, hs.last_speed,
    hs.last_speed_up, hs.last_speed_down, rfl, rfl, rfl, hs.desired_speed, rfl, hs.track_dt,
    hs.offset_vel, hs.offset_accel, hs.paused, rfl⟩, rfl⟩

/-- `stopping_distance` of a speed well below the stopping acceleration (with gain one) is the
speed itself. -/
theorem stopping_distance_small {v a : Float32} (hv : v.IsFinite) (ha : a.IsFinite)
    (hlt : |v.toReal| < a.toReal) (ha1 : 1 / 100 ≤ a.toReal) :
    (stopping_distance v 1.0 a).IsFinite ∧ (stopping_distance v 1.0 a).toReal = v.toReal := by
  have he : (2 : ℝ) ^ (-23 : ℤ) ≤ 1 / 100 := by rw [eps_eq]; norm_num
  have hpos : is_positive a = true := is_positive_of_ge ha (he.trans ha1)
  have hneg : is_negative a = false := by
    unfold is_negative
    rw [decide_eq_false_iff_not, le_iff ha neg_eps_spec.1, neg_eps_spec.2]
    have := eps_pos
    exact not_le.2 (by linarith)
  have hz : is_zero a = false := is_zero_false ha (he.trans (ha1.trans (le_abs_self _)))
  have hz1 : is_zero (1.0 : Float32) = false := is_zero_One lit_one
  have hlv := div_One_right ha lit_one
  have hvabs : v.abs < a / 1.0 := by
    rw [lt_iff ((isFinite_abs v).2 hv) hlv.1, toReal_abs, hlv.2]; exact hlt
  unfold stopping_distance inv_sqrt_controller
  simp only [hpos, hz1, hneg, hz, Bool.not_false, Bool.or_false, Bool.and_true,
    Bool.and_false, Bool.false_eq_true, if_false, if_pos hvabs]
  exact div_One_right hv lit_one

/-- The literal `3.0`. -/
theorem lit_three32 : (3.0 : Float32).IsFinite ∧ (3.0 : Float32).toReal = 3 := by
  obtain ⟨hf, hv⟩ := lit32 (x := (3.0 : Float32)) 12582912 (-22) (by decide) rfl
  exact ⟨hf, by rw [hv]; norm_num⟩

/-- **The vertical stopping point near the hover**: within `2 · 10⁻⁵` of `-1` for an altitude
estimate within `10⁻¹⁵` of `-1`, a vertical speed estimate below `1.1 · 10⁻⁵`, zero offsets and
a vertical acceleration limit of at least `1/100`. -/
theorem stopping_point_D_near (N : NarrowSpec 2) (W : WidenSpec) {psc : AC_PosControl.State}
    (hpez : Near64 psc._pos_estimate_ned_m.z (-1) 1e-15)
    (hvez : Near32 psc._vel_estimate_ned_ms.z 0 (11 / 1000000))
    (hpo : ZD psc._pos_offset_ned_m.z) (hvo : CopterZero.Z psc._vel_offset_ned_ms.z)
    (haf : psc._accel_max_d_mss.IsFinite) (ha1 : 1 / 100 ≤ psc._accel_max_d_mss.toReal) :
    Near64 (AC_PosControl.get_stopping_point_D_m runParams.psc psc) (-1) (2 / 100000) := by
  have hkP : AC_P_1D.kP runParams.psc._p_pos_d_m = 1.0 := by decide
  have hp1 : is_positive (1.0 : Float32) = true := by decide
  have he : (2 : ℝ) ^ (-23 : ℤ) ≤ 1 / 100 := by rw [eps_eq]; norm_num
  have hpa : is_positive psc._accel_max_d_mss = true := is_positive_of_ge haf (he.trans ha1)
  have hu := u32_le; have hu0 := u32_nonneg; have hη := η32_le; have hη0 := η32_nonneg
  unfold AC_PosControl.get_stopping_point_D_m
  simp only [hkP, hp1, hpa, Bool.not_true, Bool.or_false, Bool.false_eq_true, if_false]
  -- the position, narrowed, widened, offset removed, narrowed again
  have h0 := near_narrow N hpez (by norm_num)
  have h0' : Near32 (tofloat psc._pos_estimate_ned_m.z) (-1) (1 / 10000000) :=
    h0.mono (by norm_num; nlinarith)
  set c0 := tofloat psc._pos_estimate_ned_m.z with hc0
  obtain ⟨hw1, hw2⟩ : (topostype c0).IsFinite ∧ (topostype c0).toReal = c0.toReal :=
    W.exact c0 h0'.1
  obtain ⟨hd1, hd2⟩ := sub_exact_d (f := topostype c0) hw1 hpo.1 hw1 (by rw [hpo.2, sub_zero])
  have h1 : Near64 (topostype c0 - psc._pos_offset_ned_m.z) (-1) (1 / 10000000) := by
    refine ⟨hd1, ?_⟩
    rw [hd2, hw2]
    exact h0'.2
  have h2 := near_narrow N h1 (by norm_num)
  have h2' : Near32 (tofloat (topostype c0 - psc._pos_offset_ned_m.z)) (-1) (2 / 10000000) :=
    h2.mono (by norm_num; nlinarith)
  -- the velocity
  obtain ⟨hv1, hv2⟩ := sub_Z_right hvez.1 hvo
  have hv : Near32 (psc._vel_estimate_ned_ms.z - psc._vel_offset_ned_ms.z) 0 (11 / 1000000) :=
    ⟨hv1, by rw [hv2]; exact hvez.2⟩
  have hvb : |(psc._vel_estimate_ned_ms.z - psc._vel_offset_ned_ms.z).toReal| <
      psc._accel_max_d_mss.toReal := by
    have := hv.2; rw [sub_zero] at this; linarith
  obtain ⟨hs1, hs2⟩ := stopping_distance_small hv1 haf hvb ha1
  have hs : Near32 (stopping_distance (psc._vel_estimate_ned_ms.z - psc._vel_offset_ned_ms.z) 1.0
      psc._accel_max_d_mss) 0 (11 / 1000000) := ⟨hs1, by rw [hs2]; exact hv.2⟩
  have hlo : (-(3.0 : Float32)).IsFinite := (Float32.isFinite_neg _).2 lit_three32.1
  have hc := constrain_float_of_near hs hlo lit_two.1
    (by rw [Float32.toReal_neg, lit_three32.2]; norm_num) (by rw [lit_two.2]; norm_num)
  have hc' : constrain_float (stopping_distance (psc._vel_estimate_ned_ms.z -
      psc._vel_offset_ned_ms.z) 1.0 psc._accel_max_d_mss)
      (-AC_PosControl.POSCONTROL_STOPPING_DIST_UP_MAX_M)
      AC_PosControl.POSCONTROL_STOPPING_DIST_DOWN_MAX_M = stopping_distance
      (psc._vel_estimate_ned_ms.z - psc._vel_offset_ned_ms.z) 1.0 psc._accel_max_d_mss := hc
  rw [hc']
  -- the sum, widened
  have hsum := near_add (B := 2) h2' hs (by norm_num) (by norm_num)
  obtain ⟨hw3, hw4⟩ : (topostype (tofloat (topostype c0 - psc._pos_offset_ned_m.z) +
      stopping_distance (psc._vel_estimate_ned_ms.z - psc._vel_offset_ned_ms.z) 1.0
        psc._accel_max_d_mss)).IsFinite ∧ (topostype (tofloat (topostype c0 -
      psc._pos_offset_ned_m.z) + stopping_distance (psc._vel_estimate_ned_ms.z -
      psc._vel_offset_ned_ms.z) 1.0 psc._accel_max_d_mss)).toReal = (tofloat (topostype c0 -
      psc._pos_offset_ned_m.z) + stopping_distance (psc._vel_estimate_ned_ms.z -
      psc._vel_offset_ned_ms.z) 1.0 psc._accel_max_d_mss).toReal := W.exact _ hsum.1
  refine ⟨hw3, ?_⟩
  rw [hw4]
  have := hsum.2
  rw [show (-1 : ℝ) + 0 = -1 by norm_num] at this
  refine this.trans ?_
  norm_num
  nlinarith

/-- The horizontal stopping point at rest is the (zero) position estimate. -/
theorem stopping_point_NE_zero {psc : AC_PosControl.State} (hpex : ZD psc._pos_estimate_ned_m.x)
    (hpey : ZD psc._pos_estimate_ned_m.y) (hvex : CopterZero.Z psc._vel_estimate_ned_ms.x)
    (hvey : CopterZero.Z psc._vel_estimate_ned_ms.y) (hoff : OffZ psc) :
    ZD (AC_PosControl.get_stopping_point_NE_m runParams.psc psc).x ∧
      ZD (AC_PosControl.get_stopping_point_NE_m runParams.psc psc).y := by
  have hv : ZV2 (psc._vel_estimate_ned_ms.xy - psc._vel_offset_ned_ms.xy) :=
    ZV2_sub ⟨hvex, hvey⟩ hoff.2.2.2.1
  have hsp := is_positive_Z (ZV2_length hv)
  unfold AC_PosControl.get_stopping_point_NE_m
  simp only [Id.run, hsp, Bool.not_false, if_true]
  exact ⟨ZD_sub hpex hoff.2.1.1, ZD_sub hpey hoff.2.1.2⟩

/-- The binary64 literal `-1`. -/
theorem hoverWP_z_near : Near64 hoverWP.z (-1) 0 := by
  have hm : (-1 : Float).IsFinite := (Float.isFinite_neg 1).2 Float.isFinite_one
  refine ⟨hm, ?_⟩
  show |(-1 : Float).toReal - -1| ≤ 0
  rw [Float.toReal_neg, Float.toReal_one]
  simp

/-- A destination within `2 · 10⁻⁵` of the waypoint gives a leg below the `is_zero` threshold
of `calculate_track`. -/
theorem leg_is_zero (C : ConvZero) (N : NarrowSpec 2) {SP : Vector3p} (hx : ZD SP.x) (hy : ZD SP.y)
    (hz : Near64 SP.z (-1) (2 / 100000)) :
    is_zero (SP - hoverWP).tofloat.length_squared = true := by
  have hu := u32_le; have hu0 := u32_nonneg; have hη := η32_le; have hη0 := η32_nonneg
  have dx : CopterZero.Z (tofloat (SP.x - hoverWP.x)) := C.toFloat32_zero _ (ZD_sub hx ZD_zero)
  have dy : CopterZero.Z (tofloat (SP.y - hoverWP.y)) := C.toFloat32_zero _ (ZD_sub hy ZD_zero)
  have h1 := Contracts.CopterVertNear.near64_sub (B := 2) hz hoverWP_z_near (by norm_num)
    (by norm_num)
  have h2 := near_narrow N h1 (by norm_num)
  have h2' : Near32 (tofloat (SP.z - hoverWP.z)) 0 (3 / 100000) := by
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
  show is_zero (tofloat (SP.x - hoverWP.x) * tofloat (SP.x - hoverWP.x) +
    tofloat (SP.y - hoverWP.y) * tofloat (SP.y - hoverWP.y) +
    tofloat (SP.z - hoverWP.z) * tofloat (SP.z - hoverWP.z)) = true
  apply Contracts.CopterVertNear.is_zero_true hsum.1
  have := hsum.2
  rw [mul_zero, sub_zero] at this
  refine lt_of_le_of_lt this ?_
  norm_num
  nlinarith
/-- `loiter_start` as a state update: the navigator and the position controller from
`set_wp_destination_NED_m` to the stopping point, AutoYaw in `HOLD`, submode `LOITER`. -/
theorem loiter_start_eq (s : Copter.State) :
    ∃ ay : Copter.AutoYaw, Copter.ModeAuto.loiter_start runParams s =
      { s with
        wp_nav := (set_wp_destination_NED_m runParams.wpnav runParams.psc s.wp_nav s.pos_control
          (s.wpEnv runParams) (get_wp_stopping_point_NED_m runParams.psc s.pos_control)).1
        pos_control := (set_wp_destination_NED_m runParams.wpnav runParams.psc s.wp_nav
          s.pos_control (s.wpEnv runParams)
          (get_wp_stopping_point_NED_m runParams.psc s.pos_control)).2
        auto_yaw := ay
        mode_auto := { s.mode_auto with _mode := .LOITER } } ∧ ay._mode = .HOLD := by
  unfold Copter.ModeAuto.loiter_start Copter.ModeAuto.set_submode Copter.AutoYaw.set_mode
  dsimp only
  split
  · rename_i h
    exact ⟨_, rfl, by simpa using h⟩
  · exact ⟨_, rfl, rfl⟩
/-- `PreRun` does not read the navigator, the Auto mode state or AutoYaw. -/
theorem PreRun.frame {s : Copter.State} {m : AP_MotorsMulticopter.State} {ζ w : ℝ}
    (h : PreRun s m ζ w) (W : AC_WPNav.State) (ay : Copter.AutoYaw) (ma : Copter.ModeAutoState) :
    PreRun { s with wp_nav := W, auto_yaw := ay, mode_auto := ma } m ζ w := { h with }

/-! ## The tick -/

/-- The prefix of a tick leaves the scheduler as `scheduler_loop` sets it. -/
theorem prefix_scheduler (p : Copter.Parameters) (st : Copter.State) (smp : Copter.AHRS.Sample) :
    (prefixState p st smp).scheduler = (Copter.scheduler_loop st smp.dt_us).scheduler := rfl

/-- The prefix of a tick keeps the vertical acceleration limit of the position controller. -/
theorem prefix_accel_max (p : Copter.Parameters) (st : Copter.State) (smp : Copter.AHRS.Sample) :
    (prefixState p st smp).pos_control._accel_max_d_mss = st.pos_control._accel_max_d_mss := rfl

/-- **Tick 1 of the harness.** From `InvP1` (and a vertical acceleration limit of at least `1/100`,
see the header) the harness step keeps the started flag and reaches the steady invariant, with the
plant stepped by the printed actuators. -/
theorem tick_one (L : LibmZero32) (C : ConvZero) (N : CopterVertNear.NarrowSpec 2)
    (W : WidenSpec)
    {sense32 : ℝ → Float32} {senseP : ℝ → Float} (S : CopterPlant.CopterSense sense32 senseP)
    (st : Copter.State) (phys : CopterPlant.CState) (h : InvP1 st phys)
    (hA : 1 / 100 ≤ st.pos_control._accel_max_d_mss.toReal) :
    let r := CopterLift.tick runParams ⟨st, true⟩ (CopterPlant.sample sense32 senseP phys)
    r.1.started = true ∧ InvSteady r.1.st (CopterPlant.dyn phys r.2) := by
  intro r
  obtain ⟨hc, hn, hm, hpz, hvz⟩ := h
  obtain ⟨ζ, w, m, hphys, hpre, hw, hmo, -, hi, -⟩ := prefix_run L S st phys hc
  have hζ : ζ = 0 := by
    rw [hphys] at hpz
    simp only [CopterPlant.vstate] at hpz
    linarith
  have hwb : |w| ≤ 1e-5 := by
    rw [hphys] at hvz
    simpa only [CopterPlant.vstate] using hvz
  generalize hs : prefixState runParams st (CopterPlant.sample sense32 senseP phys) = s at *
  -- the clock: `millis() = 5`, three milliseconds after the last navigator update
  have hmicros : s.scheduler.micros = 5000 := by
    rw [← hs, prefix_scheduler]
    show st.scheduler.micros + CopterPlant.dtUs = 5000
    rw [hm.micros]; rfl
  have hact : AC_WPNav.is_active s.wp_nav (s.wpEnv runParams).clock = true := by
    unfold AC_WPNav.is_active
    rw [hw, hn.last_update]
    show decide (UInt32.ofNat (s.scheduler.micros / 1000) - 2 < 200) = true
    rw [hmicros]; decide
  -- the stopping point is within `2 · 10⁻⁵` of the waypoint
  have hpez : Near64 s.pos_control._pos_estimate_ned_m.z (-1) 1e-15 := by
    have := hpre.pez; rwa [hζ, zero_sub] at this
  have hvez : Near32 s.pos_control._vel_estimate_ned_ms.z 0 (11 / 1000000) := by
    refine ⟨hpre.vez.1, ?_⟩
    have h1 := abs_le.1 hpre.vez.2; have h2 := abs_le.1 hwb
    rw [sub_zero, abs_le]; constructor <;> linarith
  have hA' : 1 / 100 ≤ s.pos_control._accel_max_d_mss.toReal := by
    rw [← hs, prefix_accel_max]; exact hA
  have hNE := stopping_point_NE_zero hpre.pex hpre.pey hpre.vex hpre.vey hpre.off
  have hD := stopping_point_D_near N W hpez hvez hpre.doff.2.1 hpre.doff.2.2.2.1 hpre.psclim.amax
    hA'
  have hleg := calculate_track_empty hoverWP
    (get_wp_stopping_point_NED_m runParams.psc s.pos_control)
    (AC_PosControl.NE_get_max_speed_ms s.pos_control)
    (AC_PosControl.get_max_speed_up_ms s.pos_control)
    (AC_PosControl.get_max_speed_down_ms s.pos_control) (get_wp_acceleration_mss runParams.wpnav)
    (get_accel_D_mss runParams.wpnav) (leg_is_zero C N hNE.1 hNE.2 hD)
  -- the mission completes and `loiter_start` runs
  have hnav : NavP1 s.wp_nav := by rw [hw]; exact hn
  obtain ⟨ma, hmu, hma_w, hma_c⟩ := mission_update_complete s (by rw [hmo]; exact hm.running)
    (by rw [hmo]; exact hm.nav_cmd) (by rw [hmo]; exact hm.loaded) hnav.reached
    (by rw [hmo]; exact hm.loiter_time_max)
  obtain ⟨ay, hls, hay⟩ := loiter_start_eq { s with mode_auto := ma }
  obtain ⟨hnav', hpsc⟩ := set_wp_destination_loiter hnav s.pos_control (s.wpEnv runParams) hact
    (get_wp_stopping_point_NED_m runParams.psc s.pos_control) hleg
  have hrun : Copter.ModeAuto.run runParams s = Copter.ModeAuto.wp_run runParams
      { s with
        wp_nav := (set_wp_destination_NED_m runParams.wpnav runParams.psc s.wp_nav s.pos_control
          (s.wpEnv runParams) (get_wp_stopping_point_NED_m runParams.psc s.pos_control)).1
        pos_control := (set_wp_destination_NED_m runParams.wpnav runParams.psc s.wp_nav
          s.pos_control (s.wpEnv runParams)
          (get_wp_stopping_point_NED_m runParams.psc s.pos_control)).2
        auto_yaw := ay
        mode_auto := { ma with _mode := .LOITER } } := by
    have hws : s.mode_auto.waiting_to_start = false := by rw [hmo]; exact hm.started
    unfold Copter.ModeAuto.run
    have henv : Copter.State.wpEnv runParams { s with mode_auto := ma } = s.wpEnv runParams := rfl
    simp only [Id.run, hws, Bool.false_eq_true, if_false, hmu, hls, Copter.ModeAuto.loiter_run,
      henv]
    rfl
  generalize set_wp_destination_NED_m runParams.wpnav runParams.psc s.wp_nav s.pos_control
    (s.wpEnv runParams) (get_wp_stopping_point_NED_m runParams.psc s.pos_control) = R
    at hrun hnav' hpsc
  obtain ⟨W', P'⟩ := R
  dsimp only at hrun hnav' hpsc
  subst hpsc
  -- `wp_run` at the steady state
  generalize hs1 : ({ s with
      wp_nav := W'
      pos_control := s.pos_control
      auto_yaw := ay
      mode_auto := { ma with _mode := .LOITER } } : Copter.State) = s1 at hrun
  have hpre' : PreRun s1 m ζ w := by rw [← hs1]; exact PreRun.frame hpre W' ay _
  have hnav1 : NavSteady s1.wp_nav := by rw [← hs1]; exact hnav'
  have hay1 : s1.auto_yaw._mode = .HOLD := by rw [← hs1]; exact hay
  obtain ⟨hI, hN, hmo', hy', hi', -⟩ := wp_run_steady L C N s1 m ζ w hpre' hnav1 hay1
  have hloop := loop_prefix runParams st (CopterPlant.sample sense32 senseP phys)
    (by rw [hs, hi]; exact hm.in_auto)
  rw [hs] at hloop
  have hr : r = (⟨Copter.ModeAuto.wp_run runParams s1, true⟩,
      (Copter.ModeAuto.wp_run runParams s1).actuators) := by
    show CopterLift.tick runParams ⟨st, true⟩ (CopterPlant.sample sense32 senseP phys) = _
    unfold CopterLift.tick
    dsimp only
    rw [if_pos rfl, hloop]
    exact congrArg (fun x : Copter.State => ((⟨x, true⟩ : CopterLift.Harness), x.actuators))
      hrun
  rw [hr]
  refine ⟨rfl, ?_, hN, ?_⟩
  · have := hI (-(CopterVert.k * st.motors._throttle_filter_value.toReal))
    rw [← hphys] at this
    exact this
  · refine ⟨hi'.trans ?_, ?_, ?_, ?_, ?_⟩
    · rw [← hs1]; exact hi.trans hm.in_auto
    · rw [hmo', ← hs1]
    · rw [hmo', ← hs1]; exact hma_w.trans (by rw [hmo]; exact hm.started)
    · rw [hmo', ← hs1]; exact hma_c
    · rw [hy']; exact hay1

end Contracts.CopterHover
