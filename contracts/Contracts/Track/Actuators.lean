import FloatModel.Lit
import Contracts.Mission.Loop
import Contracts.Track.Frame

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

end Motors

end Contracts.Track
