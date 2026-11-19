import Contracts.Mission.Loop

/-!
# Q5: the mission state machine runs in order

The harness's mission (`Vehicle.lean`: `auto_run`, `mission_start`, `mission_update`,
`verify_nav_wp`, `mission_advance`, `do_nav_wp`, `set_next_wp`, `mission_complete`), along the
hidden run of `Mctrl w₀`, for every sample stream:

* `MInv`: after every tick the navigation index is in `[-1, N)`, the state is `RUNNING` (command
  loaded, index `≥ 0`) or `COMPLETE` (index `N - 1`, the last waypoint);
* `OrderStep`, `NavOrder`: from tick to tick the index never decreases, grows by at most one, and
  grows exactly when the mission was running, the navigator reported the destination reached and a
  next waypoint exists; the mission completes exactly when it was running at the last waypoint and
  the navigator reported it reached.

The proof is a frame argument: `mkey` collects the seven fields the order depends on (index,
state, command loaded, waiting to start, loiter time limit, mission, in Auto), and every function
the tick calls outside `mission_start`/`mission_update` keeps `mkey` (`mk_*`); the two loops of
the harness (`replayPos`, `applyPos`) by `forIn_array_inv`.
-/

open Vehicle

namespace Contracts.Quick

set_option linter.unusedSimpArgs false

@[simp] theorem id_pure {α : Type} (a : α) : (pure a : Id α) = a := rfl
@[simp] theorem id_run {α : Type} (a : Id α) : Id.run a = a := rfl

/-- The mission fields of the world that the harness's navigation functions leave alone. -/
def mkey (w : World) :
    Int × MissionState × Bool × Bool × UInt16 × Array AC_WPNav_lib.Vector3p.State × Bool :=
  (w.au.nav_index, w.au.state, w.au.nav_cmd_loaded, w.au.waiting_to_start, w.au.loiter_time_max,
    w.mission, w.in_auto)

theorem foldl_inv {α β : Type} (P : β → Prop) (f : β → α → β) (hf : ∀ b a, P b → P (f b a))
    (l : Array α) (b : β) (hb : P b) : P (l.foldl f b) := by
  rw [← Array.foldl_toList]
  induction l.toList generalizing b with
  | nil => exact hb
  | cons a t ih => exact ih _ (hf _ _ hb)

theorem forIn_list_inv {α β : Type} (P : β → Prop) (f : α → β → Id (ForInStep β))
    (hf : ∀ a b, P b → P (Id.run (f a b)).value) : ∀ (l : List α) (b : β), P b → P (Id.run (forIn l b f))
  | [], _, hb => hb
  | a :: t, b, hb => by
    rw [List.forIn_cons]
    have := hf a b hb
    revert this
    rcases f a b with c | c
    · exact id
    · exact fun h => forIn_list_inv P f hf t c h

theorem forIn_array_inv {α β : Type} (P : β → Prop) (f : α → β → Id (ForInStep β))
    (hf : ∀ a b, P b → P (Id.run (f a b)).value) (l : Array α) (b : β) (hb : P b) :
    P (Id.run (forIn l b f)) := by
  rw [← Array.forIn_toList]
  exact forIn_list_inv P f hf l.toList b hb

theorem replayPos_inv (P : World → Prop) (hP : ∀ w ps, P w → P { w with ps := ps }) (w : World)
    (log : AC_WPNav_lib.Outputs) (hw : P w) : P (replayPos w log) := by
  unfold replayPos
  refine forIn_array_inv P _ ?_ log w hw
  intro ev b hb
  cases ev <;> exact hP _ _ hb

theorem mk_replayPos (w : World) (log : AC_WPNav_lib.Outputs) : mkey (replayPos w log) = mkey w :=
  replayPos_inv (fun v => mkey v = mkey w) (fun _ _ h => h) w log rfl

theorem mk_afterWP (w : World) wpp wps log : mkey (afterWP w wpp wps log) = mkey w := by
  unfold afterWP; rw [mk_replayPos]; rfl

/-- The seven fields of `mkey`, as a conjunction (a form `simp` uses as seven rewrite rules). -/
def Fr (a b : World) : Prop :=
  a.au.nav_index = b.au.nav_index ∧ a.au.state = b.au.state ∧
    a.au.nav_cmd_loaded = b.au.nav_cmd_loaded ∧ a.au.waiting_to_start = b.au.waiting_to_start ∧
    a.au.loiter_time_max = b.au.loiter_time_max ∧ a.mission = b.mission ∧ a.in_auto = b.in_auto

theorem fr_of_mk {a b : World} (h : mkey a = mkey b) :
    a.au.nav_index = b.au.nav_index ∧ a.au.state = b.au.state ∧
    a.au.nav_cmd_loaded = b.au.nav_cmd_loaded ∧ a.au.waiting_to_start = b.au.waiting_to_start ∧
    a.au.loiter_time_max = b.au.loiter_time_max ∧ a.mission = b.mission ∧ a.in_auto = b.in_auto := by
  simpa [mkey] using h

theorem fr_afterWP (w : World) wpp wps log :
    (afterWP w wpp wps log).au.nav_index = w.au.nav_index ∧ (afterWP w wpp wps log).au.state = w.au.state ∧
    (afterWP w wpp wps log).au.nav_cmd_loaded = w.au.nav_cmd_loaded ∧
    (afterWP w wpp wps log).au.waiting_to_start = w.au.waiting_to_start ∧
    (afterWP w wpp wps log).au.loiter_time_max = w.au.loiter_time_max ∧
    (afterWP w wpp wps log).mission = w.mission ∧ (afterWP w wpp wps log).in_auto = w.in_auto :=
  fr_of_mk (mk_afterWP w wpp wps log)

theorem mk_withMotors (w : World) f : mkey (withMotors w f) = mkey w := by
  unfold withMotors; split; simp only [mkey]

theorem mk_applyPos (w : World) evs : mkey (applyPos w evs) = mkey w := by
  unfold applyPos
  refine forIn_array_inv (fun v => mkey v = mkey w) _ ?_ evs w rfl
  intro ev b hb
  cases ev
  simp only [id_run, id_pure, ForInStep.value]
  rw [mk_withMotors]; exact hb

theorem fr_applyPos (w : World) evs :
    (applyPos w evs).au.nav_index = w.au.nav_index ∧ (applyPos w evs).au.state = w.au.state ∧
    (applyPos w evs).au.nav_cmd_loaded = w.au.nav_cmd_loaded ∧
    (applyPos w evs).au.waiting_to_start = w.au.waiting_to_start ∧
    (applyPos w evs).au.loiter_time_max = w.au.loiter_time_max ∧
    (applyPos w evs).mission = w.mission ∧ (applyPos w evs).in_auto = w.in_auto :=
  fr_of_mk (mk_applyPos w evs)

theorem mk_auto_yaw_set_mode (w : World) m : mkey (auto_yaw_set_mode w m) = mkey w := by
  unfold auto_yaw_set_mode
  simp only [id_run]
  split
  · rfl
  · split <;> simp only [mkey, id_pure]

theorem fr_auto_yaw_set_mode (w : World) m :
    (auto_yaw_set_mode w m).au.nav_index = w.au.nav_index ∧ (auto_yaw_set_mode w m).au.state = w.au.state ∧
    (auto_yaw_set_mode w m).au.nav_cmd_loaded = w.au.nav_cmd_loaded ∧
    (auto_yaw_set_mode w m).au.waiting_to_start = w.au.waiting_to_start ∧
    (auto_yaw_set_mode w m).au.loiter_time_max = w.au.loiter_time_max ∧
    (auto_yaw_set_mode w m).mission = w.mission ∧ (auto_yaw_set_mode w m).in_auto = w.in_auto :=
  fr_of_mk (mk_auto_yaw_set_mode w m)

theorem mk_wp_run (w : World) : mkey (wp_run w) = mkey w := by
  unfold wp_run auto_yaw_get_heading auto_yaw_yaw_rad auto_yaw_rate_rads
  simp only [id_run, id_pure, mkey, fr_applyPos, fr_afterWP]

theorem mk_set_next_wp (w : World) i : mkey (set_next_wp w i).1 = mkey w := by
  unfold set_next_wp; split <;> simp only [mkey]

theorem fr_set_next_wp (w : World) i :
    (set_next_wp w i).1.au.nav_index = w.au.nav_index ∧ (set_next_wp w i).1.au.state = w.au.state ∧
    (set_next_wp w i).1.au.nav_cmd_loaded = w.au.nav_cmd_loaded ∧
    (set_next_wp w i).1.au.waiting_to_start = w.au.waiting_to_start ∧
    (set_next_wp w i).1.au.loiter_time_max = w.au.loiter_time_max ∧
    (set_next_wp w i).1.mission = w.mission ∧ (set_next_wp w i).1.in_auto = w.in_auto :=
  fr_of_mk (mk_set_next_wp w i)

theorem mk_wp_start (w : World) d : mkey (wp_start w d).1 = mkey w := by
  unfold wp_start
  simp only [id_run, id_pure]
  split <;> split <;> simp only [mkey, fr_afterWP, fr_auto_yaw_set_mode]

theorem fr_wp_start (w : World) d :
    (wp_start w d).1.au.nav_index = w.au.nav_index ∧ (wp_start w d).1.au.state = w.au.state ∧
    (wp_start w d).1.au.nav_cmd_loaded = w.au.nav_cmd_loaded ∧
    (wp_start w d).1.au.waiting_to_start = w.au.waiting_to_start ∧
    (wp_start w d).1.au.loiter_time_max = w.au.loiter_time_max ∧
    (wp_start w d).1.mission = w.mission ∧ (wp_start w d).1.in_auto = w.in_auto :=
  fr_of_mk (mk_wp_start w d)

theorem mk_do_nav_wp (w : World) i (h : w.au.loiter_time_max = 0) : mkey (do_nav_wp w i) = mkey w := by
  unfold do_nav_wp
  simp only [id_run, id_pure]
  split
  · exact mk_wp_start w _
  · simp only [mkey, fr_set_next_wp, fr_wp_start, h]

theorem mk_loiter_start (w : World) : mkey (loiter_start w).1 = mkey w := by
  unfold loiter_start
  simp only [mkey, fr_afterWP, fr_auto_yaw_set_mode]

theorem mk_mission_complete (w : World) :
    mkey (mission_complete w) = mkey { w with au.state := .COMPLETE } := by
  unfold mission_complete; rw [mk_loiter_start]

theorem verify_nav_wp_mk (w : World) : mkey (verify_nav_wp w).1 = mkey w := by
  unfold verify_nav_wp
  simp only [id_run, id_pure]
  split
  · rfl
  · split <;> split <;> simp only [mkey]

theorem verify_nav_wp_done (w : World) (h : w.au.loiter_time_max = 0) :
    (verify_nav_wp w).2 = AC_WPNav_lib.AC_WPNav.reached_wp_destination w.wps := by
  unfold verify_nav_wp
  simp only [id_run, id_pure]
  split
  · rename_i hr; simpa using hr
  · rename_i hr
    simp only [Bool.not_eq_true', Bool.not_eq_false] at hr
    rw [hr]
    split <;> split <;> simp_all

theorem fr_verify_nav_wp (w : World) :
    (verify_nav_wp w).1.au.nav_index = w.au.nav_index ∧ (verify_nav_wp w).1.au.state = w.au.state ∧
    (verify_nav_wp w).1.au.nav_cmd_loaded = w.au.nav_cmd_loaded ∧
    (verify_nav_wp w).1.au.waiting_to_start = w.au.waiting_to_start ∧
    (verify_nav_wp w).1.au.loiter_time_max = w.au.loiter_time_max ∧
    (verify_nav_wp w).1.mission = w.mission ∧ (verify_nav_wp w).1.in_auto = w.in_auto :=
  fr_of_mk (verify_nav_wp_mk w)

/-- The navigator reports the destination reached (`AC_WPNav::reached_wp_destination`). -/
def reached (w : World) : Bool := AC_WPNav_lib.AC_WPNav.reached_wp_destination w.wps

/-- The invariant of the mission state machine after every tick. -/
structure MInv (M : Array AC_WPNav_lib.Vector3p.State) (w : World) : Prop where
  mission : w.mission = M
  in_auto : w.in_auto = true
  waiting : w.au.waiting_to_start = false
  ltm : w.au.loiter_time_max = 0
  lo : -1 ≤ w.au.nav_index
  hi : w.au.nav_index < M.size
  st : w.au.state = .RUNNING ∨ w.au.state = .COMPLETE
  run : w.au.state = .RUNNING → w.au.nav_cmd_loaded = true ∧ 0 ≤ w.au.nav_index
  comp : w.au.state = .COMPLETE → w.au.nav_index + 1 = M.size

theorem MInv.congr {M} {a b : World} (h : mkey a = mkey b) (hb : MInv M b) : MInv M a := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := fr_of_mk h
  exact ⟨h6 ▸ hb.mission, h7 ▸ hb.in_auto, h4 ▸ hb.waiting, h5 ▸ hb.ltm, h1 ▸ hb.lo, h1 ▸ hb.hi,
    h2 ▸ hb.st, fun hs => h3 ▸ h1 ▸ hb.run (h2 ▸ hs), fun hs => h1 ▸ hb.comp (h2 ▸ hs)⟩

theorem mission_advance_spec (w : World) (n : Nat) (i : Int) (hs : w.au.state = .RUNNING)
    (hl : w.au.nav_cmd_loaded = false) (hsz : w.mission.size = n) (hidx : w.au.nav_index = i)
    (hi : 0 ≤ i) (hz : w.au.loiter_time_max = 0) :
    ((n : Int) ≤ i + 1 → mission_advance w = (w, false)) ∧
    (i + 1 < n →
      (mission_advance w).2 = true ∧ (mission_advance w).1.au.nav_index = i + 1 ∧
      (mission_advance w).1.au.state = .RUNNING ∧ (mission_advance w).1.au.nav_cmd_loaded = true ∧
      (mission_advance w).1.au.waiting_to_start = w.au.waiting_to_start ∧
      (mission_advance w).1.au.loiter_time_max = 0 ∧
      (mission_advance w).1.mission = w.mission ∧ (mission_advance w).1.in_auto = w.in_auto) := by
  subst hsz hidx
  have hn : ¬ w.au.nav_index < 0 := not_lt.2 hi
  refine ⟨fun hge => ?_, fun hlt => ?_⟩
  · unfold mission_advance
    simp [hs, hl, hn, hge]
  · have hlt' : ¬ ((w.mission.size : Int) ≤ w.au.nav_index + 1) := not_le.2 hlt
    have hd := fr_of_mk (mk_do_nav_wp { w with au.nav_index := w.au.nav_index + 1 }
      (w.au.nav_index + 1).toNat hz)
    simp only [mkey, hs, hl, hz] at hd
    unfold mission_advance
    simp only [hs, hl, hn, hlt', bne_self_eq_false, Bool.or_false, Bool.false_eq_true, ite_false,
      decide_false, ge_iff_le, id_run]
    simp only [hd, and_self, hz]

theorem fr_mission_complete (w : World) :
    (mission_complete w).au.nav_index = w.au.nav_index ∧ (mission_complete w).au.state = .COMPLETE ∧
    (mission_complete w).au.nav_cmd_loaded = w.au.nav_cmd_loaded ∧
    (mission_complete w).au.waiting_to_start = w.au.waiting_to_start ∧
    (mission_complete w).au.loiter_time_max = w.au.loiter_time_max ∧
    (mission_complete w).mission = w.mission ∧ (mission_complete w).in_auto = w.in_auto :=
  fr_of_mk (mk_mission_complete w)

/-- One call of `mission_update` from a world of the invariant: what happens to the navigation
index and the mission state. -/
def OrderStep (M : Array AC_WPNav_lib.Vector3p.State) (w w' : World) : Prop :=
  (w.au.state = .COMPLETE → w'.au.state = .COMPLETE ∧ w'.au.nav_index = w.au.nav_index) ∧
  (w.au.state = .RUNNING → reached w = false →
    w'.au.state = .RUNNING ∧ w'.au.nav_index = w.au.nav_index) ∧
  (w.au.state = .RUNNING → reached w = true → w.au.nav_index + 1 < M.size →
    w'.au.state = .RUNNING ∧ w'.au.nav_index = w.au.nav_index + 1) ∧
  (w.au.state = .RUNNING → reached w = true → w.au.nav_index + 1 = M.size →
    w'.au.state = .COMPLETE ∧ w'.au.nav_index = w.au.nav_index)

set_option maxHeartbeats 1000000 in
theorem mission_update_spec (w : World) {M} (hI : MInv M w) :
    MInv M (mission_update w) ∧ OrderStep M w (mission_update w) := by
  rcases hI.st with hs | hs
  · obtain ⟨hl, hi0⟩ := hI.run hs
    have hne : w.mission.isEmpty = false := by
      have := hI.hi; rw [← hI.mission] at this
      rw [Bool.eq_false_iff, ne_eq, Array.isEmpty_iff_size_eq_zero]
      omega
    have hv := verify_nav_wp_done w hI.ltm
    have fv := fr_verify_nav_wp w
    have hsr : ∀ v : World, v.au.state = .RUNNING → v.au.state ≠ .COMPLETE := by
      intro v h; rw [h]; decide
    rcases hr : reached w with _ | _
    · -- not reached: nothing changes
      have hv' : (verify_nav_wp w).2 = false := by rw [hv]; exact hr
      have heq : mission_update w = (verify_nav_wp w).1 := by
        unfold mission_update
        simp only [id_run, id_pure, hs, hne, hl, bne_self_eq_false, Bool.or_false, Bool.false_eq_true,
          ite_false, Bool.not_true, not_lt.2 hi0, decide_false, hv']
      rw [heq]
      refine ⟨hI.congr (verify_nav_wp_mk w), ?_, ?_, ?_, ?_⟩
      · intro h; exact absurd h (hsr w hs)
      · intro _ _; exact ⟨fv.2.1.trans hs, fv.1⟩
      · intro _ h; simp [hr] at h
      · intro _ h; simp [hr] at h
    · have hv' : (verify_nav_wp w).2 = true := by rw [hv]; exact hr
      have ha := mission_advance_spec { (verify_nav_wp w).1 with au.nav_cmd_loaded := false }
        M.size w.au.nav_index (by simp only [fv, hs]) rfl (by simp only [fv, hI.mission])
        (by simp only [fv]) hi0 (by simp only [fv]; exact hI.ltm)
      dsimp only at ha
      have hlt := hI.hi
      rcases lt_or_eq_of_le (show w.au.nav_index + 1 ≤ M.size by omega) with hlt' | heq'
      · obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := ha.2 hlt'
        have heq : mission_update w = (mission_advance
            { (verify_nav_wp w).1 with au.nav_cmd_loaded := false }).1 := by
          unfold mission_update
          simp only [id_run, id_pure, hs, hne, hl, bne_self_eq_false, Bool.or_false,
            Bool.false_eq_true, ite_false, Bool.not_true, not_lt.2 hi0, decide_false, hv', h1,
            ite_true, Bool.not_true]
        rw [heq]
        dsimp only
        refine ⟨⟨by rw [h7, fv.2.2.2.2.2.1, hI.mission], by rw [h8, fv.2.2.2.2.2.2, hI.in_auto],
          by rw [h5, fv.2.2.2.1, hI.waiting], h6, by rw [h2]; omega, by rw [h2]; omega,
          Or.inl h3, fun _ => ⟨h4, by rw [h2]; omega⟩, fun h => absurd h (hsr _ h3)⟩, ?_, ?_, ?_, ?_⟩
        · intro h; exact absurd h (hsr w hs)
        · intro _ h; simp [hr] at h
        · intro _ _ _; exact ⟨h3, h2⟩
        · intro _ _ h; omega
      · have hge : (M.size : Int) ≤ w.au.nav_index + 1 := heq'.symm.le
        have h0 := ha.1 hge
        have heq : mission_update w = mission_complete
            { (verify_nav_wp w).1 with au.nav_cmd_loaded := false } := by
          unfold mission_update
          simp only [id_run, id_pure, hs, hne, hl, bne_self_eq_false, Bool.or_false,
            Bool.false_eq_true, ite_false, Bool.not_true, not_lt.2 hi0, decide_false, hv', h0,
            ite_true, Bool.not_false]
        rw [heq]
        dsimp only
        have fc := fr_mission_complete { (verify_nav_wp w).1 with au.nav_cmd_loaded := false }
        dsimp only at fc
        obtain ⟨c1, c2, c3, c4, c5, c6, c7⟩ := fc
        obtain ⟨f1, f2, f3, f4, f5, f6, f7⟩ := fv
        have e1 := c1.trans f1
        refine ⟨⟨c6.trans (f6.trans hI.mission), c7.trans (f7.trans hI.in_auto),
          c4.trans (f4.trans hI.waiting), c5.trans (f5.trans hI.ltm), e1 ▸ hI.lo, e1 ▸ hI.hi, Or.inr c2,
          fun h => absurd c2 (hsr _ h), fun _ => e1 ▸ heq'⟩, ?_, ?_, ?_, ?_⟩
        · intro h; exact absurd h (hsr w hs)
        · intro _ h; simp [hr] at h
        · intro _ _ h; omega
        · intro _ _ _; exact ⟨c2, e1⟩
  · have heq : mission_update w = w := by
      unfold mission_update
      simp [hs]
    rw [heq]
    refine ⟨hI, fun _ => ⟨hs, rfl⟩, ?_, ?_, ?_⟩ <;> intro h <;> exact absurd (hs ▸ h) (by decide)

theorem withMotors_proj (w : World) f :
    (withMotors w f).au = w.au ∧ (withMotors w f).wps = w.wps ∧ (withMotors w f).mission = w.mission ∧
      (withMotors w f).in_auto = w.in_auto := by
  unfold withMotors; split; simp

theorem auto_init_proj (w : World) :
    (auto_init w).au.waiting_to_start = true ∧
      (auto_init w).au.loiter_time_max = w.au.loiter_time_max ∧
      (auto_init w).mission = w.mission := by
  unfold auto_init
  simp only [fr_afterWP, and_self]

/-- The tick is `auto_run` of a world that has the mission fields of the world before the tick
(after the first tick's `ModeAuto::init`, which sets `waiting_to_start`). -/
theorem tick_eq_auto_run (w : World) (smp : Sample) :
    ∃ w', (tick w smp).1 = auto_run w' ∧ w'.mission = w.mission ∧ w'.in_auto = true ∧
      (w.in_auto = true → w'.au = w.au ∧ w'.wps = w.wps) ∧
      (w.in_auto = false → w'.au.waiting_to_start = true ∧
        w'.au.loiter_time_max = w.au.loiter_time_max) := by
  unfold tick
  simp only [id_run, id_pure, viewUpdate, withMotors_proj]
  cases hia : w.in_auto
  · simp only [Bool.not_false, ite_true]
    refine ⟨_, rfl, ?_⟩
    simp only [auto_init_proj, withMotors_proj]
    simp
  · simp only [Bool.not_true, Bool.false_eq_true, ite_false]
    refine ⟨_, rfl, ?_⟩
    simp only [withMotors_proj, hia]
    simp

theorem takeover_proj (w : World) (smp : Sample) :
    (takeover w smp).au = w.au ∧ (takeover w smp).mission = w.mission ∧
      (takeover w smp).in_auto = w.in_auto := by
  unfold takeover
  simp only [id_run, id_pure, viewUpdate]
  by_cases hc : (w.h.start_hover != 0) = true <;> simp [hc, withMotors_proj]

theorem auto_run_running (w : World) (h : w.au.waiting_to_start = false) :
    auto_run w = wp_run (mission_update w) := by
  unfold auto_run; simp [h]

theorem auto_run_start (w : World) (h : w.au.waiting_to_start = true) :
    auto_run w = wp_run { mission_start w with au.waiting_to_start := false } := by
  unfold auto_run; simp [h]

theorem fr_do_nav_wp (w : World) i (h : w.au.loiter_time_max = 0) :
    (do_nav_wp w i).au.nav_index = w.au.nav_index ∧ (do_nav_wp w i).au.state = w.au.state ∧
    (do_nav_wp w i).au.nav_cmd_loaded = w.au.nav_cmd_loaded ∧
    (do_nav_wp w i).au.waiting_to_start = w.au.waiting_to_start ∧
    (do_nav_wp w i).au.loiter_time_max = w.au.loiter_time_max ∧
    (do_nav_wp w i).mission = w.mission ∧ (do_nav_wp w i).in_auto = w.in_auto :=
  fr_of_mk (mk_do_nav_wp w i h)

theorem mission_start_fields (w : World) (hz : w.au.loiter_time_max = 0) :
    (mission_start w).au.nav_index = (if w.mission.size = 0 then -1 else 0) ∧
      (mission_start w).au.state = (if w.mission.size = 0 then .COMPLETE else .RUNNING) ∧
      (w.mission.size ≠ 0 → (mission_start w).au.nav_cmd_loaded = true) ∧
      (mission_start w).au.loiter_time_max = 0 ∧ (mission_start w).mission = w.mission ∧
      (mission_start w).in_auto = w.in_auto := by
  rcases Nat.eq_zero_or_pos w.mission.size with h0 | hpos
  · unfold mission_start mission_advance
    simp [h0, fr_mission_complete, hz]
  · have hne : ¬ (w.mission.size : Int) ≤ 0 := by omega
    have hne' : w.mission.size ≠ 0 := by omega
    unfold mission_start mission_advance
    simp [hne, hne', fr_do_nav_wp, hz]

theorem mission_start_spec (w : World) (hz : w.au.loiter_time_max = 0) (hia : w.in_auto = true) :
    MInv w.mission { mission_start w with au.waiting_to_start := false } := by
  obtain ⟨e1, e2, e3, e4, e5, e6⟩ := mission_start_fields w hz
  rcases Nat.eq_zero_or_pos w.mission.size with h0 | hpos
  · simp only [h0, ↓reduceIte] at e1 e2
    exact ⟨e5, e6.trans hia, rfl, e4, by simp [e1], by simp [e1, e5, h0], Or.inr e2,
      fun h => absurd (e2.symm.trans h) (by decide), fun _ => by simp [e1, e5, h0]⟩
  · have hne' : w.mission.size ≠ 0 := by omega
    simp only [hne', ↓reduceIte] at e1 e2
    exact ⟨e5, e6.trans hia, rfl, e4, by simp [e1], by simp [e1, e5]; omega, Or.inl e2,
      fun _ => ⟨e3 hne', by simp [e1]⟩, fun h => absurd (e2.symm.trans h) (by decide)⟩

/-- The first tick: from a world not yet in Auto (`in_auto = false`) whose loiter time limit is
`0`, the takeover and the tick start the mission. -/
theorem first_tick (w₀ : World) (smp : Sample) (h0 : w₀.in_auto = false)
    (hz : w₀.au.loiter_time_max = 0) : MInv w₀.mission (tick (takeover w₀ smp) smp).1 := by
  obtain ⟨tk1, tk2, tk3⟩ := takeover_proj w₀ smp
  obtain ⟨w', heq, hm, hia, -, hfirst⟩ := tick_eq_auto_run (takeover w₀ smp) smp
  obtain ⟨hwt, hz'⟩ := hfirst (tk3.trans h0)
  rw [heq, auto_run_start w' hwt]
  have := mission_start_spec w' (hz'.trans (tk1 ▸ hz)) hia
  rw [hm, tk2] at this
  exact this.congr (mk_wp_run _)

theorem OrderStep.congr {M} {a a' b b' : World} (h : OrderStep M a' b') (ha : a.au = a'.au)
    (hr : reached a = reached a') (hb1 : b.au.nav_index = b'.au.nav_index)
    (hb2 : b.au.state = b'.au.state) : OrderStep M a b := by
  unfold OrderStep at h ⊢
  rw [ha, hr, hb1, hb2]
  exact h

/-- A later tick: from a world of the invariant, the tick keeps the invariant and moves the index
and the state as `OrderStep` says. -/
theorem later_tick {M} (w : World) (smp : Sample) (hI : MInv M w) :
    MInv M (tick w smp).1 ∧ OrderStep M w (tick w smp).1 := by
  obtain ⟨w', heq, hm, hia, hrun, -⟩ := tick_eq_auto_run w smp
  obtain ⟨hau, hwps⟩ := hrun hI.in_auto
  rw [heq, auto_run_running w' (by rw [hau]; exact hI.waiting)]
  have hI' : MInv M w' := by
    obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8, i9⟩ := hI
    exact ⟨hm.trans i1, hia, hau ▸ i3, hau ▸ i4, hau ▸ i5, hau ▸ i6, hau ▸ i7, hau ▸ i8, hau ▸ i9⟩
  obtain ⟨hI'', hstep⟩ := mission_update_spec w' hI'
  have hk := fr_of_mk (mk_wp_run (mission_update w'))
  refine ⟨hI''.congr (mk_wp_run _), hstep.congr hau.symm (by simp [reached, hwps]) hk.1 hk.2.1⟩

/-- The order facts of one tick, read off `OrderStep` under the invariant. -/
def NavOrder (M : Array AC_WPNav_lib.Vector3p.State) (w w' : World) : Prop :=
  w.au.nav_index ≤ w'.au.nav_index ∧ w'.au.nav_index ≤ w.au.nav_index + 1 ∧
  (w'.au.nav_index = w.au.nav_index + 1 ↔
    w.au.state = .RUNNING ∧ reached w = true ∧ w.au.nav_index + 1 < M.size) ∧
  (w'.au.state = .COMPLETE ↔
    w.au.state = .COMPLETE ∨ (w.au.state = .RUNNING ∧ reached w = true ∧ w.au.nav_index + 1 = M.size))

theorem navOrder_of_step {M} {w w' : World} (hI : MInv M w) (h : OrderStep M w w') :
    NavOrder M w w' := by
  obtain ⟨o1, o2, o3, o4⟩ := h
  have hhi := hI.hi
  have hRC : MissionState.RUNNING ≠ MissionState.COMPLETE := by decide
  rcases hI.st with hs | hs
  · rcases hr : reached w with _ | _
    · obtain ⟨a1, a2⟩ := o2 hs hr
      refine ⟨by omega, by omega, ⟨fun h => by omega, fun ⟨_, h, _⟩ => by simp [hr] at h⟩,
        ⟨fun h => ?_, ?_⟩⟩
      · exact absurd (a1.symm.trans h) hRC
      · rintro (h | ⟨-, h, -⟩)
        · exact absurd (hs.symm.trans h) hRC
        · simp [hr] at h
    · rcases lt_or_eq_of_le (show w.au.nav_index + 1 ≤ M.size by omega) with hl | he
      · obtain ⟨a1, a2⟩ := o3 hs hr hl
        refine ⟨by omega, by omega, ⟨fun _ => ⟨hs, hr, hl⟩, fun _ => a2⟩, ⟨fun h => ?_, ?_⟩⟩
        · exact absurd (a1.symm.trans h) hRC
        · rintro (h | ⟨-, -, h⟩)
          · exact absurd (hs.symm.trans h) hRC
          · omega
      · obtain ⟨a1, a2⟩ := o4 hs hr he
        refine ⟨by omega, by omega, ⟨fun h => by omega, fun ⟨_, _, h⟩ => by omega⟩,
          ⟨fun _ => Or.inr ⟨hs, hr, he⟩, fun _ => a1⟩⟩
  · obtain ⟨a1, a2⟩ := o1 hs
    refine ⟨by omega, by omega, ⟨fun h => by omega, fun ⟨h, _⟩ => absurd (hs.symm.trans h) ?_⟩,
      ⟨fun _ => Or.inl hs, fun _ => a1⟩⟩
    decide

/-- **Q5, the mission runs in order** (`Vehicle.lean`: `auto_run`, `mission_update`,
`verify_nav_wp`, `mission_advance`, `do_nav_wp`, `set_next_wp`, `mission_complete`).

Along the hidden run of `Mctrl w₀` (`s 0 = none`, `s (t+1)` the world after tick `t`), for every
sample stream (non-finite samples included, and any period `dt_us`: Q7, the samples are
unconstrained):

* after every tick the invariant `MInv` holds: the mission is `w₀`'s, the index is in
  `[-1, N)` (`N` the number of waypoints), the state is `RUNNING` (with the command loaded and the
  index `≥ 0`) or `COMPLETE` (with the index at the last waypoint, `N - 1`);
* from one tick to the next the index never decreases and grows by at most one; it grows exactly
  when the mission was running, the navigator reported the destination reached
  (`AC_WPNav::reached_wp_destination` of the world before the tick) and a next waypoint exists;
  the mission becomes (or stays) complete exactly when it was complete, or when it was running at
  the last waypoint and the navigator reported it reached.

The precondition is that `w₀` is not yet in Auto and its loiter time limit is `0`, which every
world built by `construct` and booted has (`mission_start_of_construct`). What makes it true: the
index is written only by `mission_start` (`-1`) and `mission_advance` (`+1`, or `0` from `-1`), and
`mission_advance` is reached from `mission_update` only through `verify_nav_wp`, whose result is
`reached_wp_destination` once the loiter time limit is `0` (`do_nav_wp` keeps it `0`); every other
function the tick calls leaves the mission fields alone (the `mk_*` frame lemmas). -/
theorem mission_in_order (w₀ : World) (h0 : w₀.in_auto = false) (hz : w₀.au.loiter_time_max = 0)
    {x : ℕ → Contracts.Mission.X} {s : ℕ → Option World} (hs0 : s 0 = none)
    (hs : ∀ t, (s (t + 1), (x t).out) = Contracts.Mission.tickT w₀ (s t) (x t).smp) :
    (∀ t, ∃ w, s (t + 1) = some w ∧ MInv w₀.mission w) ∧
    (∀ t w w', s (t + 1) = some w → s (t + 2) = some w' →
      OrderStep w₀.mission w w' ∧ NavOrder w₀.mission w w') := by
  have hnone : ∀ t, s t = none → s (t + 1) = some (tick (takeover w₀ (x t).smp) (x t).smp).1 := by
    intro t h; have := congrArg Prod.fst (hs t); rw [h] at this; simpa [Contracts.Mission.tickT] using this
  have hsome : ∀ t w, s t = some w → s (t + 1) = some (tick w (x t).smp).1 := by
    intro t w h; have := congrArg Prod.fst (hs t); rw [h] at this; simpa [Contracts.Mission.tickT] using this
  have hinv : ∀ t, ∃ w, s (t + 1) = some w ∧ MInv w₀.mission w := by
    intro t
    induction t with
    | zero => exact ⟨_, hnone 0 hs0, first_tick w₀ _ h0 hz⟩
    | succ t ih =>
      obtain ⟨w, hw, hI⟩ := ih
      exact ⟨_, hsome (t + 1) w hw, (later_tick w _ hI).1⟩
  refine ⟨hinv, fun t w w' hw hw' => ?_⟩
  obtain ⟨v, hv, hI⟩ := hinv t
  rw [hv] at hw; injection hw with hw; subst hw
  have h2 := hsome (t + 1) v hv
  rw [hw'] at h2; injection h2 with h2; subst h2
  have := (later_tick v (x (t + 1)).smp hI).2
  exact ⟨this, navOrder_of_step hI this⟩

/-- The precondition of `mission_in_order` holds for every booted world that `construct` builds. -/
theorem mission_start_of_construct {lines : List String} {w : World} (h : construct lines = .ok w) :
    (boot w).in_auto = false ∧ (boot w).au.loiter_time_max = 0 := by
  unfold construct at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · cases h
  · cases h; exact ⟨rfl, rfl⟩

/-- `mission_in_order` on the controller component: every behavior of `Mctrl (boot w)`, for any
`w` that `construct` builds, has its hidden run in order. -/
theorem mission_in_order_Mctrl {lines : List String} {w : World} (hc : construct lines = .ok w)
    {x : ℕ → Contracts.Mission.X} (hx : x ∈ Contracts.Mission.Mctrl (boot w)) :
    ∃ s : ℕ → Option World, s 0 = none ∧
      (∀ t, (s (t + 1), (x t).out) = Contracts.Mission.tickT (boot w) (s t) (x t).smp) ∧
      (∀ t, ∃ v, s (t + 1) = some v ∧ MInv (boot w).mission v) ∧
      (∀ t v v', s (t + 1) = some v → s (t + 2) = some v' →
        OrderStep (boot w).mission v v' ∧ NavOrder (boot w).mission v v') := by
  obtain ⟨s, hs0, hs⟩ := Contracts.Mission.mem_Mctrl.1 hx
  obtain ⟨h0, hz⟩ := mission_start_of_construct hc
  exact ⟨s, hs0, hs, mission_in_order (boot w) h0 hz hs0 hs⟩

end Contracts.Quick
