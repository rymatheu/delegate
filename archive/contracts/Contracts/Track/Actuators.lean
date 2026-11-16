import FloatModel.Lit
import Contracts.Mission.Loop
import Contracts.Mission.Spec
import Contracts.Track.Frame

/-!
# M1: the actuators are always finite and in `[0, 1]`

**The clamp.** `AP_MotorsMulticopter::set_actuator_with_slew` ends with
`constrain_value_line(input, dn, up)`. Here `dn`, `up` are the literals `0`, `1`, or (with a slew
time) themselves clamps into `[0, 1]`. `constrain_value_line` maps NaN to the midpoint
`(dn + up) / 2`, `-∞` to `dn` and `+∞` to `up`, so its result is a finite float in `[0, 1]` for
every input (`act01_set_actuator_with_slew`). `output_to_motors` writes each enabled slot with
that, or with `0` when shut down, and keeps the other slots (`actOK_output_to_motors`).

**The frame.** The rest of the tick never writes `_actuator`: the setters the attitude
controller calls, the throttle filter, the spool logic, the mixer, the navigator, the mission
logic (`act_*`, by `frame_gen`).

**Results.**
* `tick_actOK`: from a world whose 32 stored actuators are in range, on any sample (NaN and `±∞`
  entries included), `Vehicle.tick` returns actuators in range at every index (the four the harness
  reads, and the default `0` beyond). The stored actuators stay in range.
* `actuators_in_unit`: lifted to the controller component `Mctrl w₀`.
* `actuators_in_unit_mission`: the same for the mission's world (`MissionWorld w₀`). Its
  actuators start at `0`: `construct` builds `Array.replicate 32 0.0`, and `boot` does not touch it.

No precondition is needed beyond the stored actuators being in range: no parameter, no spool
state, no number of motors.
-/

namespace Contracts.Track

open AP_Motors_lib AP_MotorsMatrix


/-- A motor actuator value in range: finite, in `[0, 1]`. -/
def Act01 (a : Float32) : Prop := a.IsFinite ∧ 0 ≤ a.toReal ∧ a.toReal ≤ 1

/-- Every stored actuator slot is in range. -/
def ActOK (a : Array Float32) : Prop := ∀ (i : ℕ) (h : i < a.size), Act01 a[i]

theorem act01_zero : Act01 (0.0 : Float32) :=
  ⟨Float32.isFinite_lit_zero, by simp, by simp⟩

theorem act01_one : Act01 (1.0 : Float32) :=
  ⟨Float32.isFinite_lit_one, by simp, by simp⟩

theorem act01_default : Act01 (default : Float32) := by
  have : (default : Float32) = 0.0 := rfl
  rw [this]; exact act01_zero

theorem ActOK.getElem! {a : Array Float32} (h : ActOK a) (i : ℕ) : Act01 a[i]! := by
  by_cases hi : i < a.size
  · rw [getElem!_pos a i hi]; exact h i hi
  · rw [getElem!_neg a i hi]; exact act01_default

theorem ActOK.set! {a : Array Float32} (h : ActOK a) (i : ℕ) {v : Float32} (hv : Act01 v) :
    ActOK (a.set! i v) := by
  intro j hj
  simp only [Array.set!_eq_setIfInBounds, Array.size_setIfInBounds] at hj ⊢
  rw [Array.getElem_setIfInBounds hj]
  split
  · exact hv
  · exact h j hj

/-- The clamp of `constrain_value_line`, with both bounds in `[0, 1]`, is in `[0, 1]`, whatever
its argument (NaN goes to the midpoint). -/
theorem act01_cvl {amt lo hi : Float32} (hlo : Act01 lo) (hhi : Act01 hi) :
    Act01 (Float32.cvl amt lo hi) := by
  have hm : (1 : ℝ) ≤ Float.Model.UnpackedFloat.maxFinite32 / 2 := by
    rw [Float.Model.UnpackedFloat.maxFinite32]
    norm_num
  obtain ⟨h1, h2, h3⟩ := Float32.cvl_mem Float32.two32 (amt := amt) (A := 0) (B := 1) hlo.1 hhi.1
    (by rw [abs_le]; constructor <;> linarith [hlo.2.1, hlo.2.2])
    (by rw [abs_le]; constructor <;> linarith [hhi.2.1, hhi.2.2])
    hlo.2.1 hhi.2.1 hlo.2.2 hhi.2.2
  exact ⟨h1, h2, h3⟩

theorem cvl_eq (amt lo hi : Float32) (l : UInt32) :
    constrain_value_line_float amt lo hi l = Float32.cvl amt lo hi := rfl

/-- **`set_actuator_with_slew` always returns a finite actuator in `[0, 1]`**, for every input
(NaN and `±∞` included), every stored value and every slew parameter: its last step is
`constrain_value_line(input, dn, up)` with `dn`, `up` either the literals `0`, `1` or themselves
clamps into `[0, 1]`. -/
theorem set_actuator_with_slew_eq (p : Params) (s : State) (a input : Float32) :
    set_actuator_with_slew p s a input = Float32.cvl input
      (if is_positive_AP_Float p._slew_dn_time then
        Float32.cvl (a - s._dt_s / Float32.cvl p._slew_dn_time 0.0 0.5) 0.0 1.0 else 0.0)
      (if is_positive_AP_Float p._slew_up_time then
        Float32.cvl (a + s._dt_s / Float32.cvl p._slew_up_time 0.0 0.5) 0.0 1.0 else 1.0) := by
  simp only [set_actuator_with_slew]
  split <;> split <;> rfl

theorem act01_set_actuator_with_slew (p : Params) (s : State) (a input : Float32) :
    Act01 (set_actuator_with_slew p s a input) := by
  rw [set_actuator_with_slew_eq]
  apply act01_cvl
  · split
    · exact act01_cvl act01_zero act01_one
    · exact act01_zero
  · split
    · exact act01_cvl act01_zero act01_one
    · exact act01_one


/-! ## The motors' output path -/

section Motors

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

theorem act_check_for_failed_motor (s : State) inp x :
    (check_for_failed_motor s inp x)._actuator = s._actuator := by
  frame_gen State (fun st : State => st._actuator = s._actuator) (check_for_failed_motor s inp x)
    using first | rfl | assumption

theorem act_output_armed_stabilizing (p : Params) (s : State) inp :
    (output_armed_stabilizing p s inp)._actuator = s._actuator := by
  frame_gen State (fun st : State => st._actuator = s._actuator) (output_armed_stabilizing p s inp)
    using first | rfl | assumption | (simp only [act_check_for_failed_motor]; assumption)

theorem act_output_logic (p : Params) (s : State) : (output_logic p s).2._actuator = s._actuator := by
  frame_gen State (fun st : State => st._actuator = s._actuator) (output_logic p s) using first | rfl | assumption

theorem act_update_throttle_filter (s : State) inp :
    (update_throttle_filter s inp)._actuator = s._actuator := by
  frame_gen State (fun st : State => st._actuator = s._actuator) (update_throttle_filter s inp)
    using first | rfl | assumption

theorem act_update_external_limits (s : State) :
    (update_external_limits s)._actuator = s._actuator := by
  frame_gen State (fun st : State => st._actuator = s._actuator) (update_external_limits s)
    using first | rfl | assumption

theorem act_set_desired_spool_state (s : State) d :
    (set_desired_spool_state s d)._actuator = s._actuator := by
  frame_gen State (fun st : State => st._actuator = s._actuator) (set_desired_spool_state s d)
    using first | rfl | assumption

theorem act_set_dt_s (s : State) x : (set_dt_s s x)._actuator = s._actuator := rfl

/-- `output_to_motors` writes every enabled slot with `0` (shut down) or
`set_actuator_with_slew` (every other spool state), and keeps the others. -/
theorem actOK_output_to_motors (p : Params) (s : State) o (hs : ActOK s._actuator) :
    ActOK (output_to_motors p s o).1._actuator := by
  frame_gen State (fun st : State => ActOK st._actuator) (output_to_motors p s o) using first
    | assumption
    | (apply ActOK.set! (by assumption)
       first | exact act01_zero | exact act01_set_actuator_with_slew _ _ _ _)

/-- **The motors' output keeps the stored actuators in range.** -/
theorem actOK_output (p : Params) (s : State) o inp (hs : ActOK s._actuator) :
    ActOK (output p s o inp).2.1._actuator := by
  frame_gen State (fun st : State => ActOK st._actuator) (output p s o inp) using first
    | assumption
    | (simp only [act_update_throttle_filter, act_output_logic, act_output_armed_stabilizing,
        act_update_external_limits]; assumption)
    | exact actOK_output_to_motors _ _ _ (by assumption)

section
variable (s : State) (x : Float32)
theorem act_set_throttle_filter_cutoff : (set_throttle_filter_cutoff s x)._actuator = s._actuator := rfl
theorem act_set_throttle : (set_throttle s x)._actuator = s._actuator := rfl
theorem act_set_throttle_avg_max : (set_throttle_avg_max s x)._actuator = s._actuator := rfl
theorem act_set_roll : (set_roll s x)._actuator = s._actuator := rfl
theorem act_set_roll_ff : (set_roll_ff s x)._actuator = s._actuator := rfl
theorem act_set_pitch : (set_pitch s x)._actuator = s._actuator := rfl
theorem act_set_pitch_ff : (set_pitch_ff s x)._actuator = s._actuator := rfl
theorem act_set_yaw : (set_yaw s x)._actuator = s._actuator := rfl
theorem act_set_yaw_ff : (set_yaw_ff s x)._actuator = s._actuator := rfl
end

end Motors

/-! ## The vehicle: only the motors' output writes the actuators -/

section World

open Vehicle

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

theorem act_applyAtt (ms : State) o : (applyAtt ms o)._actuator = ms._actuator := by
  simp only [applyAtt, act_set_throttle_filter_cutoff, act_set_throttle, act_set_throttle_avg_max,
    act_set_roll, act_set_roll_ff, act_set_pitch, act_set_pitch_ff, act_set_yaw, act_set_yaw_ff]

theorem act_withMotors (w : World) f : (withMotors w f).ms._actuator = w.ms._actuator := by
  frame_gen World (fun w' : World => w'.ms._actuator = w.ms._actuator) (withMotors w f)
    using first
    | with_reducible rfl
    | with_reducible assumption
    | simp only [act_applyAtt]

theorem act_viewUpdate (w : World) : (viewUpdate w).ms = w.ms := rfl

theorem act_replayPos (w : World) log : (replayPos w log).ms._actuator = w.ms._actuator := by
  frame_gen World (fun w' : World => w'.ms._actuator = w.ms._actuator) (replayPos w log)
    using first | with_reducible rfl | with_reducible assumption

theorem act_afterWP (w : World) a b log : (afterWP w a b log).ms._actuator = w.ms._actuator := by
  simp only [afterWP, act_replayPos]

theorem act_applyPos (w : World) evs : (applyPos w evs).ms._actuator = w.ms._actuator := by
  frame_gen World (fun w' : World => w'.ms._actuator = w.ms._actuator) (applyPos w evs)
    using first
    | with_reducible rfl
    | with_reducible assumption
    | (simp only [act_withMotors] <;> with_reducible assumption)

theorem act_auto_yaw_set_mode (w : World) m :
    (auto_yaw_set_mode w m).ms._actuator = w.ms._actuator := by
  frame_gen World (fun w' : World => w'.ms._actuator = w.ms._actuator) (auto_yaw_set_mode w m)
    using first | with_reducible rfl | with_reducible assumption

theorem act_auto_yaw_get_heading (w : World) :
    (auto_yaw_get_heading w).1.ms._actuator = w.ms._actuator := rfl

theorem act_wp_start (w : World) d : (wp_start w d).1.ms._actuator = w.ms._actuator := by
  frame_gen World (fun w' : World => w'.ms._actuator = w.ms._actuator) (wp_start w d)
    using first
    | with_reducible rfl
    | with_reducible assumption
    | (simp only [act_afterWP, act_auto_yaw_set_mode] <;> with_reducible assumption)

theorem act_set_next_wp (w : World) i : (set_next_wp w i).1.ms._actuator = w.ms._actuator := by
  frame_gen World (fun w' : World => w'.ms._actuator = w.ms._actuator) (set_next_wp w i)
    using first | with_reducible rfl | with_reducible assumption

theorem act_do_nav_wp (w : World) i : (do_nav_wp w i).ms._actuator = w.ms._actuator := by
  frame_gen World (fun w' : World => w'.ms._actuator = w.ms._actuator) (do_nav_wp w i)
    using first
    | with_reducible rfl
    | with_reducible assumption
    | (simp only [act_wp_start, act_set_next_wp] <;> with_reducible assumption)

theorem act_verify_nav_wp (w : World) : (verify_nav_wp w).1.ms._actuator = w.ms._actuator := by
  frame_gen World (fun w' : World => w'.ms._actuator = w.ms._actuator) (verify_nav_wp w)
    using first | with_reducible rfl | with_reducible assumption

theorem act_loiter_start (w : World) : (loiter_start w).1.ms._actuator = w.ms._actuator := by
  frame_gen World (fun w' : World => w'.ms._actuator = w.ms._actuator) (loiter_start w)
    using first
    | with_reducible rfl
    | with_reducible assumption
    | (simp only [act_afterWP, act_auto_yaw_set_mode] <;> with_reducible assumption)

theorem act_mission_complete (w : World) :
    (mission_complete w).ms._actuator = w.ms._actuator := by
  simp only [mission_complete, act_loiter_start]

theorem act_mission_advance (w : World) :
    (mission_advance w).1.ms._actuator = w.ms._actuator := by
  frame_gen World (fun w' : World => w'.ms._actuator = w.ms._actuator) (mission_advance w)
    using first
    | with_reducible rfl
    | with_reducible assumption
    | (simp only [act_do_nav_wp] <;> with_reducible assumption)

theorem act_mission_start (w : World) : (mission_start w).ms._actuator = w.ms._actuator := by
  frame_gen World (fun w' : World => w'.ms._actuator = w.ms._actuator) (mission_start w)
    using first
    | with_reducible rfl
    | with_reducible assumption
    | (simp only [act_mission_advance, act_mission_complete] <;> with_reducible assumption)

theorem act_mission_update (w : World) : (mission_update w).ms._actuator = w.ms._actuator := by
  frame_gen World (fun w' : World => w'.ms._actuator = w.ms._actuator) (mission_update w)
    using first
    | with_reducible rfl
    | with_reducible assumption
    | (simp only [act_mission_advance, act_mission_complete, act_verify_nav_wp] <;>
       with_reducible assumption)

theorem act_auto_init (w : World) : (auto_init w).ms._actuator = w.ms._actuator := by
  frame_gen World (fun w' : World => w'.ms._actuator = w.ms._actuator) (auto_init w)
    using first
    | with_reducible rfl
    | with_reducible assumption
    | (simp only [act_afterWP] <;> with_reducible assumption)

theorem act_wp_run (w : World) : (wp_run w).ms._actuator = w.ms._actuator := by
  frame_gen World (fun w' : World => w'.ms._actuator = w.ms._actuator) (wp_run w)
    using first
    | with_reducible rfl
    | with_reducible assumption
    | (simp only [act_afterWP, act_applyPos, act_set_desired_spool_state,
        act_auto_yaw_get_heading] <;> with_reducible assumption)

theorem act_auto_run (w : World) : (auto_run w).ms._actuator = w.ms._actuator := by
  frame_gen World (fun w' : World => w'.ms._actuator = w.ms._actuator) (auto_run w)
    using first
    | with_reducible rfl
    | with_reducible assumption
    | (simp only [act_mission_start, act_mission_update, act_wp_run] <;> with_reducible assumption)

/-- The four slots the harness reads, `#[a[0]!, …, a[3]!]`, are in range when `a` is. -/
theorem actOK_lit4 {a : Array Float32} (h : ActOK a) :
    ActOK (#[a[0]!, a[1]!, a[2]!, a[3]!] : Array Float32) := by
  intro j hj
  match j, hj with
  | 0, _ => exact h.getElem! 0
  | 1, _ => exact h.getElem! 1
  | 2, _ => exact h.getElem! 2
  | 3, _ => exact h.getElem! 3

/-- **M1, one tick.** From any world whose stored actuators are in `[0, 1]`, on any sample
(NaN and `±∞` entries included), the tick returns actuators that are finite and in `[0, 1]` (at
every index: the four it reads, and the default `0` beyond), and leaves the stored actuators in
`[0, 1]`. -/
theorem tick_actOK (w : World) (smp : Sample) (hw : ActOK w.ms._actuator) :
    ActOK (tick w smp).1.ms._actuator ∧ ∀ i : ℕ, Act01 (tick w smp).2[i]! := by
  frame_genN [World, State, Array Float32]
    [fun w' : World => ActOK w'.ms._actuator, fun s : State => ActOK s._actuator,
      fun a : Array Float32 => ∀ i : ℕ, Act01 a[i]!] (tick w smp) using first
    | with_reducible assumption
    | (simp only [act_set_dt_s, act_withMotors, act_viewUpdate, act_auto_init, act_auto_run] <;>
       with_reducible assumption)
    | exact actOK_output _ _ _ _ (by assumption)
    | exact fun i => (actOK_lit4 (by assumption)).getElem! i

theorem actOK_takeover (w : World) (smp : Sample) (hw : ActOK w.ms._actuator) :
    ActOK (takeover w smp).ms._actuator := by
  frame_gen World (fun w' : World => ActOK w'.ms._actuator) (takeover w smp) using first
    | with_reducible assumption
    | (simp only [act_withMotors, act_viewUpdate] <;> with_reducible assumption)

end World

/-! ## M1 on the controller component -/

section Lifted

open Vehicle Contracts.Mission

/-- One controller step keeps the hidden world's actuators in range and outputs four actuators in
range, from any hidden state whose world (if any) has its actuators in range. -/
theorem tickT_actOK (w₀ : World) (h₀ : ActOK w₀.ms._actuator) (s : Option World)
    (hs : ∀ w, s = some w → ActOK w.ms._actuator) (smp : Sample) :
    (∀ w, (tickT w₀ s smp).1 = some w → ActOK w.ms._actuator) ∧
      ∀ i : Fin 4, Act01 (tickT w₀ s smp).2.act[i] := by
  have hwa : ActOK (match s with | some w => w | none => takeover w₀ smp).ms._actuator := by
    cases s with
    | some w => exact hs w rfl
    | none => exact actOK_takeover w₀ smp h₀
  obtain ⟨h1, h2⟩ := tick_actOK _ smp hwa
  refine ⟨fun w hw => ?_, fun i => ?_⟩
  · simp only [tickT, Option.some.injEq] at hw
    rw [← hw]; exact h1
  · match i with
    | ⟨0, _⟩ => exact h2 0
    | ⟨1, _⟩ => exact h2 1
    | ⟨2, _⟩ => exact h2 2
    | ⟨3, _⟩ => exact h2 3

/-- **M1 (`actuators_in_unit`).** For every initial world whose stored actuators are in `[0, 1]`,
every behavior of the controller component `Mctrl w₀` outputs, at every tick, four actuators that
are finite and in `[0, 1]`, whatever its samples are (NaN and `±∞` included). -/
theorem actuators_in_unit (w₀ : World) (h₀ : ActOK w₀.ms._actuator) {x : ℕ → X}
    (hx : x ∈ Mctrl w₀) (t : ℕ) (i : Fin 4) : Act01 ((x t).out.act[i]) := by
  obtain ⟨s, hs0, hstep⟩ := mem_Mctrl.1 hx
  have inv : ∀ t, ∀ w, s t = some w → ActOK w.ms._actuator := by
    intro t
    induction t with
    | zero => intro w hw; rw [hs0] at hw; cases hw
    | succ t ih =>
      intro w hw
      have := congrArg Prod.fst (hstep t)
      simp only at this
      rw [this] at hw
      exact (tickT_actOK w₀ h₀ (s t) ih (x t).smp).1 w hw
  have := congrArg Prod.snd (hstep t)
  simp only at this
  rw [this]
  exact (tickT_actOK w₀ h₀ (s t) (inv t) (x t).smp).2 i

/-! ## The mission's initial world -/

theorem actOK_replicate (n : ℕ) : ActOK (Array.replicate n (0.0 : Float32)) := by
  intro i hi
  rw [Array.getElem_replicate]
  exact act01_zero

theorem construct_ms (lines : List String) (w : World) (h : Vehicle.construct lines = .ok w) :
    w.ms = (AP_Motors_lib.AP_MotorsMatrix.construct 400).2 := by
  unfold Vehicle.construct at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · simp only [pure, Except.pure, Except.ok.injEq] at h
    rw [← h]

set_option maxHeartbeats 4000000 in
theorem actOK_motors_construct :
    ActOK (AP_Motors_lib.AP_MotorsMatrix.construct 400).2._actuator := by
  frame_gen AP_Motors_lib.AP_MotorsMatrix.State
    (fun s : AP_Motors_lib.AP_MotorsMatrix.State => ActOK s._actuator)
    (AP_Motors_lib.AP_MotorsMatrix.construct 400) using first
    | with_reducible assumption
    | exact actOK_replicate _

set_option maxHeartbeats 4000000 in
theorem actOK_boot (w : World) (hw : ActOK w.ms._actuator) : ActOK (boot w).ms._actuator := by
  frame_genN [World, AP_Motors_lib.AP_MotorsMatrix.State]
    [fun w' : World => ActOK w'.ms._actuator,
     fun s : AP_Motors_lib.AP_MotorsMatrix.State => ActOK s._actuator] (boot w) using first
    | with_reducible assumption
    | exact actOK_replicate _

/-- The mission's initial world (`MissionWorld`: booted from `construct`) has its actuators in
range (all `0`). -/
theorem actOK_missionWorld {w₀ : World} (hM : MissionWorld w₀) : ActOK w₀.ms._actuator := by
  obtain ⟨w, hw, rfl⟩ := hM.built
  apply actOK_boot
  rw [construct_ms _ w hw]
  exact actOK_motors_construct

/-- **M1 for the mission flights**: the controller built from the course parameter files outputs
finite actuators in `[0, 1]` at every tick of every behavior. -/
theorem actuators_in_unit_mission {w₀ : World} (hM : MissionWorld w₀) {x : ℕ → X}
    (hx : x ∈ Mctrl w₀) (t : ℕ) (i : Fin 4) : Act01 ((x t).out.act[i]) :=
  actuators_in_unit w₀ (actOK_missionWorld hM) hx t i

end Lifted

end Contracts.Track
