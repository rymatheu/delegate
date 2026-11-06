import Contracts.Track.CtrlVertical

/-!
# The navigator's frame for the vertical loop (`NavV`)

`vertical_tick_eq` takes the navigator's frame `NavV` as a hypothesis: between the estimates and
`D_update_controller`, the mission update and `update_wpnav` (with its replayed calls into the
position controller) leave alone the vertical loop's PID states, the estimates, the period, the
motors' throttle filter, the motors' parameters and the sample. This file discharges

* the motors' and the sample's part (`NF`) for the whole mission harness, unconditionally
  (`nf_mission_update`, `nf_navW`);
* the position controller's part (`VF`) for every call the navigator replays except
  `D_init_controller_stopping_point` (`vf_replayPos`, `vf_navW`), which re-initializes the vertical
  controller and is excluded by a hypothesis on the log;

and assembles `NavV` from the two (`navV_mk`, `navV_of_logs`).
-/

namespace Contracts.Track.CtrlV

open Vehicle AC_PosControl_lib

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

/-- What the navigator leaves alone: the motors' throttle filter, the motors' parameters, the
sample. -/
abbrev NF (w w' : World) : Prop :=
  w'.ms._throttle_filter = w.ms._throttle_filter ∧ w'.mp = w.mp ∧ w'.sample = w.sample

theorem nf_replayPos (w : World) log : NF w (replayPos w log) := by
  frame_gen World (fun w' : World => NF w w') (replayPos w log)
    using first | exact ⟨rfl, rfl, rfl⟩ | with_reducible rfl | with_reducible assumption

theorem nf_afterWP (w : World) a b log : NF w (afterWP w a b log) := by
  simp only [afterWP]; exact nf_replayPos _ _

theorem nf_auto_yaw_set_mode (w : World) m : NF w (auto_yaw_set_mode w m) := by
  frame_gen World (fun w' : World => NF w w') (auto_yaw_set_mode w m)
    using first | exact ⟨rfl, rfl, rfl⟩ | with_reducible rfl | with_reducible assumption

theorem nf_trans {a b c : World} (h1 : NF a b) (h2 : NF b c) : NF a c :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.trans h1.2.2⟩

theorem nf_wp_start (w : World) d : NF w (wp_start w d).1 := by
  frame_gen World (fun w' : World => NF w w') (wp_start w d)
    using first
    | exact ⟨rfl, rfl, rfl⟩
    | with_reducible assumption
    | exact nf_trans (by assumption) (nf_afterWP _ _ _ _)
    | exact nf_trans (by assumption) (nf_auto_yaw_set_mode _ _)
    | (exact ⟨(by assumption : NF w _).1, (by assumption : NF w _).2.1, (by assumption : NF w _).2.2⟩)


theorem nf_set_next_wp (w : World) i : NF w (set_next_wp w i).1 := by
  unfold set_next_wp; split <;> exact ⟨rfl, rfl, rfl⟩

theorem nf_au (w : World) a : NF w { w with au := a } := ⟨rfl, rfl, rfl⟩

theorem nf_do_nav_wp (w : World) i : NF w (do_nav_wp w i) := by
  have h := nf_wp_start w w.mission[i]!
  unfold do_nav_wp
  dsimp only [Id.run]
  rcases hw : wp_start w w.mission[i]! with ⟨w1, ok⟩
  rw [hw] at h
  cases ok
  · simp only [Bool.not_false, ite_true]; exact h
  · simp only [Bool.not_true, Bool.false_eq_true, ite_false]
    exact nf_trans h (nf_trans (nf_au w1 _) (nf_set_next_wp _ _))

theorem nf_verify_nav_wp (w : World) : NF w (verify_nav_wp w).1 := by
  unfold verify_nav_wp
  dsimp only [Id.run]
  split
  · exact ⟨rfl, rfl, rfl⟩
  · split <;> (try split) <;> exact ⟨rfl, rfl, rfl⟩

theorem nf_loiter_start (w : World) : NF w (loiter_start w).1 := by
  unfold loiter_start
  exact nf_trans (nf_afterWP _ _ _ _) (nf_auto_yaw_set_mode _ _)

theorem nf_mission_complete (w : World) : NF w (mission_complete w) := by
  unfold mission_complete
  exact nf_trans (nf_au w _) (nf_loiter_start _)

theorem nf_adv_aux (w : World) (index : Int) :
    NF w (if index ≥ w.mission.size then (w, false) else
      ({ (do_nav_wp { w with au.nav_index := index } index.toNat) with au.nav_cmd_loaded := true }, true)).1 := by
  split
  · exact ⟨rfl, rfl, rfl⟩
  · exact nf_trans (nf_trans (nf_au w _) (nf_do_nav_wp _ _)) (nf_au _ _)

theorem nf_mission_advance (w : World) : NF w (mission_advance w).1 := by
  unfold mission_advance
  split
  · exact ⟨rfl, rfl, rfl⟩
  · exact nf_adv_aux w _

theorem nf_mission_update (w : World) : NF w (mission_update w) := by
  unfold mission_update
  dsimp only [Id.run]
  split
  · exact ⟨rfl, rfl, rfl⟩
  · split
    · split
      · exact nf_trans (nf_mission_advance w) (nf_mission_complete _)
      · exact nf_mission_advance w
    · split
      · split
        · exact nf_trans (nf_trans (nf_verify_nav_wp w) (nf_trans (nf_au _ _) (nf_mission_advance _))) (nf_mission_complete _)
        · exact nf_trans (nf_verify_nav_wp w) (nf_trans (nf_au _ _) (nf_mission_advance _))
      · exact nf_verify_nav_wp w

theorem nf_navW (w : World) : NF w (navW w) := by
  unfold navW
  exact nf_trans (b := { w with ms := AP_Motors_lib.AP_MotorsMatrix.set_desired_spool_state w.ms .THROTTLE_UNLIMITED }) ⟨by simp only [AP_Motors_lib.AP_MotorsMatrix.set_desired_spool_state]; split <;> rfl, rfl, rfl⟩ (nf_afterWP _ _ _ _)

/-- The fields of the position controller that the vertical loop reads and that the navigator's
calls leave alone (except `D_init_controller_stopping_point`). -/
abbrev VF (s s' : AC_PosControl.State) : Prop :=
  s'._pid_vel_d_m = s._pid_vel_d_m ∧ s'._pid_accel_d_m = s._pid_accel_d_m ∧
  s'._pos_estimate_ned_m = s._pos_estimate_ned_m ∧ s'._vel_estimate_ned_ms = s._vel_estimate_ned_ms ∧
  s'._dt_s = s._dt_s

macro "vf_leaf" : tactic => `(tactic| first
  | exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | with_reducible assumption
  | exact ⟨(by assumption : VF _ _).1, (by assumption : VF _ _).2.1, (by assumption : VF _ _).2.2.1, (by assumption : VF _ _).2.2.2.1, (by assumption : VF _ _).2.2.2.2⟩)

theorem vf_init_pos_terrain (s : AC_PosControl.State) d : VF s (AC_PosControl.init_pos_terrain_D_m s d) := by
  frame_gen AC_PosControl.State (fun s' => VF s s') (AC_PosControl.init_pos_terrain_D_m s d) using vf_leaf

theorem vf_set_pos_terrain (s : AC_PosControl.State) d : VF s (AC_PosControl.set_pos_terrain_target_D_m s d) := by
  frame_gen AC_PosControl.State (fun s' => VF s s') (AC_PosControl.set_pos_terrain_target_D_m s d) using vf_leaf

theorem vf_set_pva (s : AC_PosControl.State) a b c : VF s (AC_PosControl.set_pos_vel_accel_NED_m s a b c) := by
  frame_gen AC_PosControl.State (fun s' => VF s s') (AC_PosControl.set_pos_vel_accel_NED_m s a b c) using vf_leaf

theorem vf_D_max (p) (s : AC_PosControl.State) a b c : VF s (AC_PosControl.D_set_max_speed_accel_m p s a b c) := by
  frame_gen AC_PosControl.State (fun s' => VF s s') (AC_PosControl.D_set_max_speed_accel_m p s a b c) using vf_leaf

theorem vf_D_corr (p) (s : AC_PosControl.State) a b c : VF s (AC_PosControl.D_set_correction_speed_accel_m p s a b c) := by
  frame_gen AC_PosControl.State (fun s' => VF s s') (AC_PosControl.D_set_correction_speed_accel_m p s a b c) using vf_leaf

theorem vf_NE_max (p) (s : AC_PosControl.State) i a b : VF s (AC_PosControl.NE_set_max_speed_accel_m p s i a b) := by
  frame_gen AC_PosControl.State (fun s' => VF s s') (AC_PosControl.NE_set_max_speed_accel_m p s i a b) using vf_leaf

theorem vf_NE_corr (p) (s : AC_PosControl.State) a b : VF s (AC_PosControl.NE_set_correction_speed_accel_m p s a b) := by
  frame_gen AC_PosControl.State (fun s' => VF s s') (AC_PosControl.NE_set_correction_speed_accel_m p s a b) using vf_leaf

theorem vf_trans {a b c : AC_PosControl.State} (h1 : VF a b) (h2 : VF b c) : VF a c :=
  ⟨h2.1.trans h1.1, h2.2.1.trans h1.2.1, h2.2.2.1.trans h1.2.2.1, h2.2.2.2.1.trans h1.2.2.2.1, h2.2.2.2.2.trans h1.2.2.2.2⟩

theorem vf_NE_init_offsets (s : AC_PosControl.State) i : VF s (AC_PosControl.NE_init_offsets s i) := by
  frame_gen AC_PosControl.State (fun s' => VF s s') (AC_PosControl.NE_init_offsets s i) using vf_leaf

theorem vf_NE_init_ekf_reset (s : AC_PosControl.State) i : VF s (AC_PosControl.NE_init_ekf_reset s i) := by
  frame_gen AC_PosControl.State (fun s' => VF s s') (AC_PosControl.NE_init_ekf_reset s i) using vf_leaf

theorem vf_NE_handle_ekf_reset (s : AC_PosControl.State) i : VF s (AC_PosControl.NE_handle_ekf_reset s i) := by
  frame_gen AC_PosControl.State (fun s' => VF s s') (AC_PosControl.NE_handle_ekf_reset s i) using vf_leaf

theorem vf_NE_update_offsets (s : AC_PosControl.State) i : VF s (AC_PosControl.NE_update_offsets s i) := by
  frame_gen AC_PosControl.State (fun s' => VF s s') (AC_PosControl.NE_update_offsets s i) using vf_leaf

theorem vf_yaw (s : AC_PosControl.State) i : VF s (AC_PosControl.calculate_yaw_and_rate_yaw s i) := by
  frame_gen AC_PosControl.State (fun s' => VF s s') (AC_PosControl.calculate_yaw_and_rate_yaw s i) using vf_leaf

macro "vf_call" : tactic => `(tactic| first
  | vf_leaf
  | exact vf_trans (by assumption) (vf_NE_init_offsets _ _)
  | exact vf_trans (by assumption) (vf_NE_init_ekf_reset _ _)
  | exact vf_trans (by assumption) (vf_NE_handle_ekf_reset _ _)
  | exact vf_trans (by assumption) (vf_NE_update_offsets _ _)
  | exact vf_trans (by assumption) (vf_yaw _ _)
  | exact vf_trans (by assumption) (vf_NE_init _ _ _))

theorem vf_NE_init (p) (s : AC_PosControl.State) i : VF s (AC_PosControl.NE_init_controller p s i) := by
  frame_gen AC_PosControl.State (fun s' => VF s s') (AC_PosControl.NE_init_controller p s i) using vf_call

theorem vf_NE_init_sp (p) (s : AC_PosControl.State) i : VF s (AC_PosControl.NE_init_controller_stopping_point p s i) := by
  frame_gen AC_PosControl.State (fun s' => VF s s') (AC_PosControl.NE_init_controller_stopping_point p s i) using vf_call

theorem vf_NE_update (p) (s : AC_PosControl.State) i : VF s (AC_PosControl.NE_update_controller p s i) := by
  frame_gen AC_PosControl.State (fun s' => VF s s') (AC_PosControl.NE_update_controller p s i) using vf_call

theorem forIn_list_mem_inv {α β : Type} (P : β → Prop) (f : α → β → Id (ForInStep β)) (l : List α)
    (hf : ∀ a ∈ l, ∀ b, P b → P (Id.run (f a b)).value) (b : β) (hb : P b) :
    P (Id.run (forIn l b f)) := by
  induction l generalizing b with
  | nil => exact hb
  | cons a as ih =>
    rw [List.forIn_cons]
    have h1 := hf a List.mem_cons_self b hb
    revert h1
    show P (Id.run (f a b)).value → P (Id.run (match Id.run (f a b) with
        | ForInStep.done b => (pure b : Id β)
        | ForInStep.yield b => forIn as b f))
    cases Id.run (f a b) with
    | done c => exact fun h => h
    | yield c => exact fun h => ih (fun a' ha' => hf a' (List.mem_cons_of_mem _ ha')) c h

theorem forIn_array_mem_inv {α β : Type} (P : β → Prop) (f : α → β → Id (ForInStep β)) (l : Array α)
    (hf : ∀ a ∈ l.toList, ∀ b, P b → P (Id.run (f a b)).value) (b : β) (hb : P b) :
    P (Id.run (forIn l b f)) := by
  rw [← Array.forIn_toList]
  exact forIn_list_mem_inv P f l.toList hf b hb

/-- The navigator's calls into the position controller leave the vertical loop's fields alone,
unless the log holds a `D_init_controller_stopping_point` (which re-initializes the vertical
controller). -/
theorem vf_replayPos (w : World) (log : AC_WPNav_lib.Outputs)
    (h : ∀ ev ∈ log.toList, ev ≠ .D_init_controller_stopping_point) : VF w.ps (replayPos w log).ps := by
  unfold replayPos
  refine forIn_array_mem_inv (fun v : World => VF w.ps v.ps) _ log ?_ w ⟨rfl, rfl, rfl, rfl, rfl⟩
  intro ev hev b hb
  cases ev with
  | init_pos_terrain_D_m d => exact vf_trans hb (vf_init_pos_terrain _ _)
  | D_init_controller_stopping_point => exact absurd rfl (h _ hev)
  | NE_init_controller_stopping_point => exact vf_trans hb (vf_NE_init_sp _ _ _)
  | NE_set_max_speed_accel_m v a => exact vf_trans hb (vf_NE_max _ _ _ _ _)
  | NE_set_correction_speed_accel_m v a => exact vf_trans hb (vf_NE_corr _ _ _ _)
  | D_set_max_speed_accel_m dn up a => exact vf_trans hb (vf_D_max _ _ _ _ _)
  | D_set_correction_speed_accel_m dn up a => exact vf_trans hb (vf_D_corr _ _ _ _ _)
  | set_pos_terrain_target_D_m d => exact vf_trans hb (vf_set_pos_terrain _ _)
  | set_pos_vel_accel_NED_m pos vel acc => exact vf_trans hb (vf_set_pva _ _ _ _)
  | NE_update_controller => exact vf_trans hb (vf_NE_update _ _ _)

theorem vf_afterWP (w : World) a b (log : AC_WPNav_lib.Outputs)
    (h : ∀ ev ∈ log.toList, ev ≠ .D_init_controller_stopping_point) : VF w.ps (afterWP w a b log).ps :=
  vf_replayPos _ log h

/-- The world `update_wpnav` reads in `wp_run`: the motors' spool state set. -/
def navPre (w : World) : World :=
  { w with ms := AP_Motors_lib.AP_MotorsMatrix.set_desired_spool_state w.ms .THROTTLE_UNLIMITED }

/-- The calls `update_wpnav` logs in `wp_run`. -/
def navLog (w : World) : AC_WPNav_lib.Outputs :=
  (AC_WPNav_lib.AC_WPNav.update_wpnav (navPre w).wpp (navPre w).wps #[] (wpInputs (navPre w))).2.1

theorem vf_navW (w : World) (h : ∀ ev ∈ (navLog w).toList, ev ≠ .D_init_controller_stopping_point) :
    VF w.ps (navW w).ps := by
  unfold navLog navPre at h
  unfold navW
  dsimp only at h ⊢
  generalize AC_WPNav_lib.AC_WPNav.update_wpnav w.wpp w.wps #[]
    (wpInputs { w with ms := AP_Motors_lib.AP_MotorsMatrix.set_desired_spool_state w.ms .THROTTLE_UNLIMITED }) = r at h ⊢
  rcases r with ⟨wps, log, x⟩
  exact vf_afterWP _ _ _ _ h

theorem vf_verify_nav_wp (w : World) : VF w.ps (verify_nav_wp w).1.ps := by
  unfold verify_nav_wp
  dsimp only [Id.run]
  split
  · exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  · split <;> (try split) <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- The mission update on a tick with a loaded waypoint not yet reached leaves the world's
position controller alone. -/
theorem mission_update_steady (w : World) (hrun : w.au.state = .RUNNING) (hne : w.mission.isEmpty = false)
    (hl : w.au.nav_cmd_loaded = true) (hi : ¬ w.au.nav_index < 0) (hv : (verify_nav_wp w).2 = false) :
    (mission_update w).ps = w.ps := by
  unfold mission_update
  simp only [Id.run, hrun, hne, hl, hi, hv, bne_self_eq_false, Bool.false_or, Bool.not_true,
    decide_false, Bool.or_false, Bool.false_eq_true, ite_false]
  unfold verify_nav_wp at hv ⊢
  dsimp only [Id.run] at hv ⊢
  split <;> (try split) <;> (try split) <;> simp_all

/-- `NavV` from the position controller's part. -/
theorem navV_mk (w smp) (h : VF (preAuto (postMot (preMot w smp)) smp).ps (navOf w smp).ps) :
    NavV (preAuto (postMot (preMot w smp)) smp) (navOf w smp) :=
  have hn := nf_trans (nf_mission_update (preAuto (postMot (preMot w smp)) smp)) (nf_navW _)
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2, hn.1, hn.2.1, hn.2.2⟩

/-- `NavV` on a tick whose mission update keeps the position controller and whose `update_wpnav`
log holds no `D_init_controller_stopping_point`. -/
theorem navV_of_logs (w smp)
    (hm : (mission_update (preAuto (postMot (preMot w smp)) smp)).ps = (preAuto (postMot (preMot w smp)) smp).ps)
    (h : ∀ ev ∈ (navLog (mission_update (preAuto (postMot (preMot w smp)) smp))).toList,
      ev ≠ .D_init_controller_stopping_point) :
    NavV (preAuto (postMot (preMot w smp)) smp) (navOf w smp) := by
  refine navV_mk w smp ?_
  have := vf_navW _ h
  rw [hm] at this
  exact this

end Contracts.Track.CtrlV
