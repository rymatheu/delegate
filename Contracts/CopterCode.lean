import Contracts.Basic
import Contracts.CopterLift
import Contracts.Float32ClipAP

/-!
# Code-only contracts of the ArduCopter port: actuator range

`actuators_in_unit P : Mcopter P ⊨ ⟨Afin, Gunit⟩`: for every parameter record `P` and every input
stream whatsoever (`Afin = Set.univ`: NaN and infinities included, any `dt_us`), every actuator at
every tick is a finite `Float32` with real value in `[0, 1]`. No hypothesis on the parameters is
needed.

The proof follows the last operation on each actuator, `constrain_float input dn up` at the end of
`AP_MotorsMulticopter::set_actuator_with_slew` (`AP_MotorsMulticopter.cpp:510`):

* `dn` is `0` or a `constrain_float _ 0 1`, and `up` is `1` or a `constrain_float _ 0 1`, so both
  are finite and in `[0, 1]` for every input (`Float32Clip.constrain_float_spec` with the bounds
  `0, 1`, whose sum cannot overflow). They need not be ordered: with `MOT_SLEW_UP_TIME`,
  `MOT_SLEW_DN_TIME` positive and a non-finite slew step they can cross.
* `constrain_float x lo hi` is finite and in `[0, 1]` for every `x` and every finite `lo, hi` in
  `[0, 1]`, ordered or not (`constrain_unit`). On a NaN input it returns the binary32 midpoint
  `(lo + hi) / 2`; its overflow caveat (`Float32Clip.constrain_float_nan_overflow`) is discharged
  by `lo + hi ∈ [0, 2]`, and rounding does not cross the floats `0`, `2`, then `0`, `1`
  (`midpoint_unit`). This is the case that `Float32Clip.midpoint_spec` leaves out (it needs
  `lo ≤ hi`).

The chain is local, as `QuadCode.step_motors` is: `set_actuator_with_slew_unit`, then
`output_to_motors_unit`, then `output_unit`, then `loop_unit`, then `tick_unit`. One fact is not
local: `output_to_motors` leaves the slots of disabled motors at their previous `_actuator`
value, so the theorem carries the invariant "`motors._actuator` is finite in `[0, 1]`" along the
hidden state (`Inv`), which holds at boot (`_actuator` is constructed zero) and is kept by every
tick, since the loop stores the vector it outputs (`motors._actuator = actuators`) and nothing
else in the loop writes `_actuator` or `actuators` (the `*_same` lemmas).
-/

namespace Contracts.CopterCode

open Float.Model UnpackedFloat AP_Math Copter Contracts.CopterLift Contracts.Lift

/-! ## Predicates on signals -/

/-- An actuator value that is a finite float in `[0, 1]`. -/
def UnitAct (u : Float32) : Prop := u.IsFinite ∧ 0 ≤ u.toReal ∧ u.toReal ≤ 1

/-- All four actuator values are finite and in `[0, 1]`. -/
def ActUnit (a : Vector Float32 4) : Prop := ∀ i : Fin 4, UnitAct a[i]

theorem unit_zero : UnitAct 0 := ⟨Float32.isFinite_zero, by simp, by simp⟩

theorem unit_one : UnitAct 1 := ⟨Float32.isFinite_one, by simp, by simp⟩

theorem actUnit_zero : ActUnit #v[0.0, 0.0, 0.0, 0.0] := by
  intro i; fin_cases i <;> exact unit_zero

theorem actUnit_set {a : Vector Float32 4} (ha : ActUnit a) {v : Float32} (hv : UnitAct v)
    (i : Fin 4) : ActUnit (a.set i v i.isLt) := by
  intro j
  simp only [Fin.getElem_fin, Vector.getElem_set]
  split
  · exact hv
  · exact ha j

/-! ## `constrain_float` with bounds in `[0, 1]` -/

/-- The binary32 midpoint of two finite floats in `[0, 1]`, in either order, is finite and in
`[0, 1]`. -/
theorem midpoint_unit {lo hi : Float32} (hlo : UnitAct lo) (hhi : UnitAct hi) :
    UnitAct ((lo + hi) / 2) := by
  obtain ⟨flo, l0, l1⟩ := hlo
  obtain ⟨fhi, h0, h1⟩ := hhi
  have hM := Float32.one_le_maxFinite32
  have hsum : |lo.toReal + hi.toReal| ≤ maxFinite32 := by
    rw [abs_of_nonneg (by linarith)]
    have h2 : (2 : ℝ) ≤ maxFinite32 := by
      rw [Float32.maxFinite32_eq]
      have : (2 : ℝ) ^ (-23 : ℤ) ≤ 1 := zpow_le_one_of_nonpos₀ (by norm_num) (by norm_num)
      have : (2 : ℝ) ≤ 2 ^ (127 : ℤ) := by
        calc (2 : ℝ) = 2 ^ (1 : ℤ) := by norm_num
          _ ≤ 2 ^ (127 : ℤ) := zpow_le_zpow_right₀ (by norm_num) (by norm_num)
      nlinarith
    linarith
  obtain ⟨fs, -⟩ := Float32.add_err_all flo fhi hsum
  have s0 := (Float32.add_bracket flo fhi hsum Float32.isFinite_zero).1 (by simp; linarith)
  have s2 := (Float32.add_bracket flo fhi hsum Float32Clip.isFinite_two).2
    (by rw [Float32Clip.toReal_two]; linarith)
  rw [Float32.toReal_zero] at s0
  rw [Float32Clip.toReal_two] at s2
  have h20 : (2 : Float32).toReal ≠ 0 := by rw [Float32Clip.toReal_two]; norm_num
  have hq : |(lo + hi).toReal / (2 : Float32).toReal| ≤ maxFinite32 := by
    rw [Float32Clip.toReal_two, abs_of_nonneg (by linarith)]
    linarith
  obtain ⟨fq, -⟩ := Float32.div_err_all fs Float32Clip.isFinite_two h20 hq
  have q0 := (Float32.div_bracket fs Float32Clip.isFinite_two h20 hq Float32.isFinite_zero).1
    (by rw [Float32.toReal_zero, Float32Clip.toReal_two]; linarith)
  have q1 := (Float32.div_bracket fs Float32Clip.isFinite_two h20 hq Float32.isFinite_one).2
    (by rw [Float32.toReal_one, Float32Clip.toReal_two]; linarith)
  rw [Float32.toReal_zero] at q0
  rw [Float32.toReal_one] at q1
  exact ⟨fq, q0, q1⟩

/-- **`constrain_float` with finite bounds in `[0, 1]`, ordered or not, is finite and in `[0, 1]`
for every input**, NaN and infinities included. -/
-- <<constrain_unit>>
theorem constrain_unit {lo hi : Float32} (hlo : UnitAct lo) (hhi : UnitAct hi) (x : Float32) :
    UnitAct (constrain_float x lo hi) := by
  -- <</constrain_unit>>
  unfold constrain_float
  split
  · exact midpoint_unit hlo hhi
  next hn =>
    split
    · exact hlo
    next h1 =>
      split
      · exact hhi
      next h2 =>
        have hx := Float32Clip.isFinite_of_not_lt_of_not_lt hlo.1 hhi.1 hn h1 h2
        refine ⟨hx, ?_, ?_⟩
        · have := not_lt.1 fun h => h1 ((Float32.lt_iff_toReal_lt hx hlo.1).2 h)
          linarith [hlo.2.1]
        · have := not_lt.1 fun h => h2 ((Float32.lt_iff_toReal_lt hhi.1 hx).2 h)
          linarith [hhi.2.2]

theorem constrain01_unit (x : Float32) : UnitAct (constrain_float x 0.0 1.0) :=
  constrain_unit unit_zero unit_one x

/-! ## `AP_MotorsMulticopter::set_actuator_with_slew` (`AP_MotorsMulticopter.cpp:484-511`) -/

/-- The slew limits are `0` or a `constrain_float _ 0 1` (below) and `1` or a
`constrain_float _ 0 1` (above), and the result is `constrain_float input dn up`
(`AP_MotorsMulticopter.cpp:510`). -/
-- <<set_actuator_with_slew_eq>>
theorem set_actuator_with_slew_eq (p : AP_MotorsMulticopter.Params) (s : AP_MotorsMulticopter.State)
    (actuator_output input : Float32) :
    ∃ dn up, (dn = 0.0 ∨ ∃ y, dn = constrain_float y 0.0 1.0) ∧
      (up = 1.0 ∨ ∃ y, up = constrain_float y 0.0 1.0) ∧
      AP_MotorsMulticopter.set_actuator_with_slew p s actuator_output input =
        constrain_float input dn up := by
  -- <</set_actuator_with_slew_eq>>
  unfold AP_MotorsMulticopter.set_actuator_with_slew
  dsimp only [Id.run, pure, bind]
  split <;> split
  all_goals
    exact ⟨_, _, by first | exact Or.inl rfl | exact Or.inr ⟨_, rfl⟩,
      by first | exact Or.inl rfl | exact Or.inr ⟨_, rfl⟩, rfl⟩

/-- **`set_actuator_with_slew` is finite and in `[0, 1]`** for every parameter record, state,
previous output and input. -/
-- <<set_actuator_with_slew_unit>>
theorem set_actuator_with_slew_unit (p : AP_MotorsMulticopter.Params)
    (s : AP_MotorsMulticopter.State) (actuator_output input : Float32) :
    UnitAct (AP_MotorsMulticopter.set_actuator_with_slew p s actuator_output input) := by
  -- <</set_actuator_with_slew_unit>>
  obtain ⟨dn, up, hdn, hup, h⟩ := set_actuator_with_slew_eq p s actuator_output input
  rw [h]
  refine constrain_unit ?_ ?_ input
  · rcases hdn with rfl | ⟨y, rfl⟩
    · exact unit_zero
    · exact constrain01_unit y
  · rcases hup with rfl | ⟨y, rfl⟩
    · exact unit_one
    · exact constrain01_unit y

/-! ## `AP_MotorsMatrix::output_to_motors` and `AP_MotorsMulticopter::output` -/

/-- An invariant of the loop state of a `for` loop in `Id` holds after the loop. -/
theorem forIn_inv {α σ : Type} (P : σ → Prop) (f : α → σ → Id (ForInStep σ))
    (hf : ∀ a r, P r → P (f a r).run.value) :
    ∀ (l : List α) (init : σ), P init → P (forIn l init f).run := by
  intro l
  induction l with
  | nil => intro init h; simpa using h
  | cons a l ih =>
    intro init h
    rw [List.forIn_cons]
    have := hf a init h
    cases hfa : (f a init) with
    | done b => rw [hfa] at this; exact this
    | yield b => rw [hfa] at this; exact ih b this

/-- `output_to_motors` (`AP_MotorsMatrix.cpp:144-184`): if the stored actuators are in range, so is
the output, and the stored actuators become the output. A disabled slot keeps its stored value; an
enabled slot is `set_actuator_with_slew`. -/
-- <<output_to_motors_unit>>
theorem output_to_motors_unit (p : AP_MotorsMulticopter.Params) (s : AP_MotorsMatrix.State)
    (h : ActUnit s._actuator) :
    ActUnit (AP_MotorsMatrix.output_to_motors p s).2 ∧
      (AP_MotorsMatrix.output_to_motors p s).1._actuator = (AP_MotorsMatrix.output_to_motors p s).2 := by
  -- <</output_to_motors_unit>>
  unfold AP_MotorsMatrix.output_to_motors
  dsimp only [Id.run, pure, bind]
  refine ⟨?_, rfl⟩
  refine forIn_inv ActUnit _ ?_ _ _ h
  intro i r hr
  split
  · exact actUnit_set hr (set_actuator_with_slew_unit _ _ _ _) i
  · exact hr

/-- A projection of an `if` whose two branches have the same projection. -/
theorem ite_proj_eq {α β : Type} {c : Prop} [Decidable c] {a b : α} (f : α → β) {x : β}
    (ha : f a = x) (hb : f b = x) : f (if c then a else b) = x := by
  split <;> assumption

theorem update_throttle_filter_actuator (s : AP_MotorsMulticopter.State) :
    (AP_MotorsMulticopter.update_throttle_filter s)._actuator = s._actuator := by
  unfold AP_MotorsMulticopter.update_throttle_filter
  dsimp only [Id.run, pure, bind]
  repeat' (first | rfl |
    refine ite_proj_eq (fun t : AP_MotorsMulticopter.State => t._actuator) ?_ ?_)

theorem output_logic_actuator (p : AP_MotorsMulticopter.Params) (s : AP_MotorsMulticopter.State) :
    (AP_MotorsMulticopter.output_logic p s)._actuator = s._actuator := by
  unfold AP_MotorsMulticopter.output_logic AP_MotorsMulticopter.get_current_limit_max_throttle
  dsimp only [Id.run, pure, bind]
  repeat' (first | rfl |
    refine ite_proj_eq (fun t : AP_MotorsMulticopter.State => t._actuator) ?_ ?_)

theorem output_armed_stabilizing_actuator (p : AP_MotorsMulticopter.Params)
    (s : AP_MotorsMatrix.State) :
    (AP_MotorsMatrix.output_armed_stabilizing p s)._actuator = s._actuator := by
  unfold AP_MotorsMatrix.output_armed_stabilizing
  dsimp only [Id.run, pure, bind]
  repeat' (first | rfl |
    refine ite_proj_eq (fun t : AP_MotorsMatrix.State => t._actuator) ?_ ?_)

/-- `output` (`AP_MotorsMulticopter.cpp:273-304`): the throttle filter, the battery reset, the
spool logic and `output_armed_stabilizing` leave `_actuator` alone; `output_to_motors` does the
rest. -/
-- <<output_unit>>
theorem output_unit (p : AP_MotorsMulticopter.Params) (s : AP_MotorsMatrix.State)
    (h : ActUnit s._actuator) :
    ActUnit (AP_MotorsMatrix.output p s).2 ∧
      (AP_MotorsMatrix.output p s).1._actuator = (AP_MotorsMatrix.output p s).2 := by
  -- <</output_unit>>
  unfold AP_MotorsMatrix.output
  dsimp only
  apply output_to_motors_unit
  rw [output_armed_stabilizing_actuator]
  show ActUnit (AP_MotorsMulticopter.output_logic p _)._actuator
  rw [output_logic_actuator]
  show ActUnit (AP_MotorsMulticopter.update_throttle_filter s.toState)._actuator
  rw [update_throttle_filter_actuator]
  exact h

/-! ## `Copter.loop` -/

/-- `s'` has the stored motor actuators and the output actuators of `s`. -/
def Same (s s' : State) : Prop := s'.motors._actuator = s.motors._actuator ∧ s'.actuators = s.actuators

theorem Same.trans {a b c : State} (h1 : Same a b) (h2 : Same b c) : Same a c :=
  ⟨h2.1.trans h1.1, h2.2.trans h1.2⟩

section Frame

open ModeAuto

theorem set_mode_same (s : State) (m : AutoYawMode) : Same s (AutoYaw.set_mode s m) := by
  unfold AutoYaw.set_mode; split <;> exact ⟨rfl, rfl⟩

theorem get_heading_same (s : State) : Same s (AutoYaw.get_heading s).1 := by
  unfold AutoYaw.get_heading AutoYaw.yaw_rad AutoYaw.rate_rads AutoYaw.look_ahead_yaw_rad
  dsimp only
  repeat' split
  all_goals exact ⟨rfl, rfl⟩

theorem wp_run_same (p : Parameters) (s : State) : Same s (wp_run p s) := by
  unfold wp_run
  dsimp only [Id.run, pure]
  refine Same.trans ?_ (get_heading_same _)
  exact ⟨rfl, rfl⟩

theorem set_submode_same (s : State) (m : SubMode) : Same s (set_submode s m) := ⟨rfl, rfl⟩

theorem init_same (p : Parameters) (s s' : State) (h : ModeAuto.init p s = some s') : Same s s' := by
  unfold ModeAuto.init at h
  split at h
  · cases h
  · cases h; exact ⟨rfl, rfl⟩

theorem set_next_wp_same (p : Parameters) (s : State) (c : MissionCommand) :
    Same s (set_next_wp p s c) := by
  unfold set_next_wp; repeat' split
  all_goals exact ⟨rfl, rfl⟩

theorem wp_start_same (p : Parameters) (s : State) (d : Vector3p) : Same s (wp_start p s d) := by
  unfold wp_start
  dsimp only [Id.run, pure]
  split
  all_goals
    refine Same.trans ?_ (set_submode_same _ _)
    refine Same.trans ?_ (set_mode_same _ _)
    exact ⟨rfl, rfl⟩

theorem do_nav_wp_same (p : Parameters) (s : State) (c : MissionCommand) :
    Same s (do_nav_wp p s c) := by
  unfold do_nav_wp
  refine Same.trans ?_ (set_next_wp_same _ _ _)
  exact Same.trans (wp_start_same p s _) ⟨rfl, rfl⟩

theorem verify_nav_wp_same (s : State) : Same s (verify_nav_wp s).1 := by
  unfold verify_nav_wp
  dsimp only
  repeat' split
  all_goals exact ⟨rfl, rfl⟩

theorem loiter_start_same (p : Parameters) (s : State) : Same s (loiter_start p s) := by
  unfold loiter_start
  refine Same.trans ?_ (set_submode_same _ _)
  refine Same.trans ?_ (set_mode_same _ _)
  exact ⟨rfl, rfl⟩

theorem mission_complete_same (p : Parameters) (s : State) : Same s (mission_complete p s) := by
  unfold mission_complete exit_mission
  exact Same.trans ⟨rfl, rfl⟩ (loiter_start_same _ _)

theorem advance_same (p : Parameters) (s s' : State) (h : advance_current_nav_cmd p s = some s') :
    Same s s' := by
  unfold advance_current_nav_cmd at h
  dsimp only at h
  split_ifs at h
  split at h
  · cases h
  · cases h; exact Same.trans ⟨rfl, rfl⟩ (do_nav_wp_same _ _ _)

theorem mission_start_same (p : Parameters) (s : State) : Same s (mission_start p s) := by
  unfold mission_start
  dsimp only
  split
  next h => refine Same.trans ?_ (advance_same p _ _ h); exact ⟨rfl, rfl⟩
  next => refine Same.trans ?_ (mission_complete_same p _); exact ⟨rfl, rfl⟩

theorem mission_update_same (p : Parameters) (s : State) : Same s (mission_update p s) := by
  unfold mission_update
  dsimp only
  split
  · exact ⟨rfl, rfl⟩
  split
  · split
    next h => exact advance_same p s _ h
    next => exact mission_complete_same p s
  · have h1 := verify_nav_wp_same s
    split
    · split
      next h => refine Same.trans h1 (Same.trans ?_ (advance_same p _ _ h)); exact ⟨rfl, rfl⟩
      next => refine Same.trans h1 (Same.trans ?_ (mission_complete_same p _)); exact ⟨rfl, rfl⟩
    · exact h1

/-- `ModeAuto::run` writes neither the stored nor the output actuators. -/
theorem run_same (p : Parameters) (s : State) : Same s (ModeAuto.run p s) := by
  unfold ModeAuto.run loiter_run
  dsimp only [Id.run, pure]
  split
  all_goals
    split
    all_goals
      refine Same.trans ?_ (wp_run_same p _)
      first
        | (refine Same.trans (mission_start_same p s) ?_; exact ⟨rfl, rfl⟩)
        | exact mission_update_same p s

end Frame

theorem enter_auto_same (p : Parameters) (s s' : State) (h : enter_auto p s = some s') :
    Same s s' := by
  unfold enter_auto at h
  cases hi : ModeAuto.init p s with
  | none => rw [hi] at h; cases h
  | some s₁ =>
    rw [hi] at h
    cases h
    exact Same.trans (init_same p s s₁ hi) ⟨rfl, rfl⟩

/-- The state after `motors_output_main`, in the order of `Copter.loop`. -/
def afterMotors (p : Parameters) (s : State) (smp : AHRS.Sample) : State :=
  motors_output_main p (run_rate_controller_main p (ins_update (scheduler_loop s smp.dt_us) smp))

/-- After `motors_output_main` the tick's actuators are in range and stored in the motors object. -/
theorem afterMotors_unit (p : Parameters) (s : State) (smp : AHRS.Sample)
    (h : ActUnit s.motors._actuator) :
    ActUnit (afterMotors p s smp).actuators ∧
      (afterMotors p s smp).motors._actuator = (afterMotors p s smp).actuators := by
  unfold afterMotors motors_output_main
  dsimp only
  exact output_unit _ _ h

/-- The rest of the tick, after `motors_output_main`, leaves both actuator vectors alone. -/
theorem loop_same (p : Parameters) (s s' : State) (smp : AHRS.Sample) (h : loop p s smp = some s') :
    Same (afterMotors p s smp) s' := by
  unfold loop at h
  dsimp only at h
  split at h
  · cases h
    exact Same.trans ⟨rfl, rfl⟩ (run_same p _)
  · cases he : enter_auto p (read_inertia (read_AHRS (afterMotors p s smp) smp)) with
    | none =>
      unfold afterMotors at he
      rw [he] at h; cases h
    | some s₁ =>
      have he' := he
      unfold afterMotors at he'
      rw [he'] at h
      cases h
      exact Same.trans (Same.trans (⟨rfl, rfl⟩ : Same (afterMotors p s smp)
        (read_inertia (read_AHRS (afterMotors p s smp) smp)))
        (enter_auto_same p _ s₁ he)) (run_same p s₁)

/-- **One tick of `Copter.loop`.** If the stored actuators are in range, then the output actuators
of the tick are in range and stored. -/
-- <<loop_unit>>
theorem loop_unit (p : Parameters) (s s' : State) (smp : AHRS.Sample)
    (hs : ActUnit s.motors._actuator) (h : loop p s smp = some s') :
    ActUnit s'.actuators ∧ ActUnit s'.motors._actuator := by
  -- <</loop_unit>>
  obtain ⟨h1, h2⟩ := afterMotors_unit p s smp hs
  obtain ⟨e1, e2⟩ := loop_same p s s' smp h
  refine ⟨e2 ▸ h1, ?_⟩
  rw [e1, h2]; exact h1

/-! ## The harness and the boot state -/

theorem takeover_actuator (p : Parameters) (s : State) (smp : AHRS.Sample) :
    (takeover p s smp).motors._actuator = s.motors._actuator := by
  unfold takeover
  dsimp only
  split <;> rfl

theorem add_motors_actuator (s : AP_MotorsMatrix.State) (m : Vector AP_MotorsMatrix.MotorDef 4) :
    (AP_MotorsMatrix.add_motors s m)._actuator = s._actuator := by
  unfold AP_MotorsMatrix.add_motors
  refine forIn_inv (fun t : AP_MotorsMatrix.State => t._actuator = s._actuator) _ ?_ _ _ rfl
  intro i r hr
  show (AP_MotorsMatrix.add_motor_raw r i _ _ _ _)._actuator = s._actuator
  unfold AP_MotorsMatrix.add_motor_raw
  rw [← hr]
  split <;> rfl

theorem normalise_rpy_factors_actuator (s : AP_MotorsMatrix.State) :
    (AP_MotorsMatrix.normalise_rpy_factors s)._actuator = s._actuator := by
  unfold AP_MotorsMatrix.normalise_rpy_factors
  dsimp only [Id.run, pure, bind]
  refine forIn_inv (fun t : AP_MotorsMatrix.State => t._actuator = s._actuator) _ ?_ _ _ rfl
  intro i r hr
  split
  · rw [← hr]
    repeat' (first | rfl |
      refine ite_proj_eq (fun t : ForInStep AP_MotorsMatrix.State => t.value._actuator) ?_ ?_)
  · exact hr

theorem setup_motors_actuator (s : AP_MotorsMatrix.State) :
    (AP_MotorsMatrix.setup_motors s)._actuator = s._actuator := by
  unfold AP_MotorsMatrix.setup_motors AP_MotorsMatrix.setup_quad_matrix
  dsimp only [Id.run, pure, bind]
  rw [normalise_rpy_factors_actuator, add_motors_actuator]
  refine forIn_inv (fun t : AP_MotorsMatrix.State => t._actuator = s._actuator) _ ?_ _ _ rfl
  intro i r hr
  exact hr

/-- At boot `_actuator` is zero. -/
theorem init_actuator (P : Parameters) :
    (State.init P).motors._actuator = #v[0.0, 0.0, 0.0, 0.0] := by
  unfold State.init AP_MotorsMatrix.init
  exact setup_motors_actuator _

/-- The invariant carried along the hidden state. -/
def Inv (h : Harness) : Prop := ActUnit h.st.motors._actuator

theorem init_inv (P : Parameters) : Inv (Harness.init P) := by
  unfold Inv Harness.init
  rw [init_actuator]
  exact actUnit_zero

/-- **One step of the executable.** The invariant is kept and the output is in range. -/
-- <<tick_unit>>
theorem tick_unit (P : Parameters) (h : Harness) (smp : AHRS.Sample) (hi : Inv h) :
    Inv (tick P h smp).1 ∧ ActUnit (tick P h smp).2 := by
  -- <</tick_unit>>
  have hst : ActUnit (if h.started then h.st else takeover P h.st smp).motors._actuator := by
    split
    · exact hi
    · rw [takeover_actuator]; exact hi
  unfold tick
  dsimp only
  split
  next st' hl =>
    obtain ⟨a1, a2⟩ := loop_unit P _ st' smp hst hl
    exact ⟨a2, a1⟩
  next => exact ⟨hst, actUnit_zero⟩

/-! ## `actuators_in_unit` -/

/-- Assumption: none. Every input stream, NaN and infinities included. -/
-- <<Afin>>
def Afin : Set (ℕ → CX) := Set.univ
-- <</Afin>>

/-- Guarantee: every actuator at every tick is a finite `Float32` in `[0, 1]`. -/
-- <<Gunit>>
def Gunit : Set (ℕ → CX) := {x | ∀ t, ActUnit (x t).act}
-- <</Gunit>>

/-- **Actuator range.** The ArduCopter port with any parameters implements `⟨Afin, Gunit⟩`. -/
-- <<actuators_in_unit>>
theorem actuators_in_unit (P : Parameters) : Mcopter P ⊨ ⟨Afin, Gunit⟩ := by
  rintro x ⟨⟨s, h0, hs⟩, -⟩ t
  have hinv : ∀ t, Inv (s t) := by
    intro t
    induction t with
    | zero => rw [h0]; exact init_inv P
    | succ n ih =>
      have := congrArg Prod.fst (hs n)
      simp only at this
      rw [this]; exact (tick_unit P _ _ ih).1
  have := congrArg Prod.snd (hs t)
  simp only at this
  rw [this]; exact (tick_unit P _ _ (hinv t)).2
-- <</actuators_in_unit>>

/-- The port with the built-in parameters meets the actuator-range contract. -/
theorem actuators_in_unit_defaults : McopterDefaults ⊨ ⟨Afin, Gunit⟩ := actuators_in_unit defaults

/-- The contract is not vacuous: the port has behaviors, and the assumption is everything. -/
theorem actuators_in_unit_nonvacuous (P : Parameters) : (Mcopter P ∩ Afin).Nonempty := by
  obtain ⟨x, hx⟩ := Mcopter_nonempty P
  exact ⟨x, hx, Set.mem_univ _⟩

/-! ## Inventory for the finiteness phase (comment, not a proof)

`QuadCode.controller_finite` was cheap because every stored integral of the old controller was the
output of a clip and every stored error a difference of a clipped setpoint and the sample. In the
port most stored floats are not. Below: every stored floating-point field of `Copter.State`
reached by `Copter.loop`, grouped by library, that is NOT the output of a clip/`constrain_float`
with finite bounds, a literal, a parameter copy or a copy of the sample, with the writer and the
lemma it needs. (Free fields are listed at the end of each group in one line.) Tags:

* [ALPHA] `calc_lowpass_alpha_dt dt fc ∈ [0,1]` for every finite `dt ≥ 0` and every finite `fc`.
* [LPF] first-order filter under rounding: `x' = x + a(y - x)`, `a ∈ [0,1]` finite,
  `|y| ≤ B`, `|x| ≤ B(1+2u)` gives `|x'| ≤ B(1+2u)`, `u = 2^-24` (a convex combination; the
  slack is needed, otherwise the bound degrades each tick).
* [DQ] difference quotient `(e - e_last)/dt` behind `is_positive dt`; `dt = ofNat dt_us * 1e-6`
  is `0` or `≥ 1e-6` (first tick `1/400`), so `|q| ≤ 2B·10^6(1+u)`.
* [SHAPE] `shape_accel(_xy)` stays between the old acceleration and a target clipped to `±amax`:
  `|a| ≤ amax(1+2u)` is invariant.
* [FBINT] feedback integrator `v += a·dt` with `|a| ≤ amax` and no clamp: a horizon bound
  `|v_n| ≤ |v_0| + n·amax·dtmax` (finite but not uniform), or a tracking invariant of
  `shape_*_vel_accel` (uniform, needs a `sqrt_controller` analysis).
* [LIMLEN] `limit_length(_xy)`, `limit_accel_xy`: `|out| ≤ max(1+2u)` only on a finite input
  (`∞ · (max/∞) = ∞ · 0 = NaN`).
* [QUAT] `‖pq‖ ≤ ‖p‖‖q‖(1+cu)`; `normalize` gives norm `≤ 1+cu` when `‖q‖ ≥ FLT_EPSILON`, else
  leaves `q`; needs `‖q_sample‖ ≤ Bq`.
* [TRIG] `sin`, `cos`, `tan`, `acos`, `atan`, `atan2` are opaque: hypotheses (finite on finite
  arguments, `sin, cos ∈ [-1,1]`, `acos ∈ [0,π]`, `atan2 ∈ [-π,π]`, `tan` finite below 80°).
* [DIV] division with a guarded denominator `|d| ≥ d0 > 0`.
* [NARROW] `tofloat : Float → Float32` finite iff `|x| ≲ FLT_MAX`.
* [LIN] polynomial in bounded finite terms: finite if the polynomial bound is below `FLT_MAX`.
* [MINMAX] `MIN`/`MAX` are ternaries on `<`/`>`, not clips: finite only if both arguments are
  (NaN passes in one argument order, `±∞` passes always).
* [ZERO] exact-zero invariant (up to the sign of zero) of `update_pos_vel_accel(_xy)` and
  `shape_pos_vel_accel(_xy)` started at zero with a zero target; an invariant of reachable states.
* [EXIT] `AC_PID.update_all`, `AC_PID_Basic.update_all`, `AC_PID_2D.update_all` return the state
  unchanged on a non-finite target or measurement, so only overflow from finite inputs matters.

Global hypotheses the phase will need: finite moderate parameters; `|vel|, |accel_ef|, |gyro| ≤ B`,
`|pos| ≤ Bp`, `‖quat‖ ≤ Bq`; `dt_us ≤ DTMAX` (`Float32.ofNat dt_us` finite and the integrators
scale with it).

### Copter (`Copter/Loop.lean`, `Copter/AHRS.lean`, `Copter/AutoYaw.lean`)
- `scheduler.last_loop_time_s`: `scheduler_loop`, `ofNat dt_us * 1e-6` — finite iff `dt_us < 2^128`;
  the `dt` of every library below.
- `ahrs.rot_body_to_ned`: `Quaternion.rotation_matrix` of the sample — [LIN], quadratic in `q`.
- `ahrs.roll, pitch, yaw`: `Matrix3f.to_euler` (`atan2`, `safe_asin`) — [TRIG].
- `ahrs.sin_roll`: `calc_trig`, `rot.c.y / cp` with `cp ≥ FLT_EPSILON`, not constrained; `cos/sin`
  of roll on the fallback — [DIV] + [TRIG] (exceeds 1 for a non-unit `q`). `ahrs.sin_pitch`:
  `-rot.c.x` — [LIN].
- `auto_yaw._look_ahead_yaw_rad`: `atan2` of the velocity — [TRIG] (LOOK_AHEAD only).
  `auto_yaw._yaw_angle_rad`, `_yaw_rate_rads`: copies of controller targets, written, never read.
- Free: `ins_gyro`, `ahrs.quat_body_to_ned, gyro_latest, accel_ef, vel_ned, pos_ned` (sample);
  `ahrs.cos_yaw, sin_yaw, cos_pitch, cos_roll` (`constrain_float`); `actuators` (this file);
  `_pilot_yaw_rate_rads` (literal); mission locations (parameters).

### AP_Motors (`AP_Motors/*.lean`)
- `_roll_in, _pitch_in, _yaw_in`: `rate_controller_run_dt`, rate-PID `P + D + I`, unclamped —
  [LIN] in the `AC_PID` bounds below (`I` clipped, `D` through [DQ]).
- `_roll_in_ff, _pitch_in_ff, _yaw_in_ff`: `get_ff = target·FF + target_derivative·D_FF` (yaw
  times `_feedforward_scalar ∈ [0,1]`) — [LIN] + [DQ].
- `_throttle_in`: `set_throttle_out`, `throttle_in · inverted_factor · boost`, `throttle_in` the
  unclamped vertical-acceleration PID output of `AC_PosControl` — [LIN].
- `_throttle_filter_value`: `update_throttle_filter`, [LPF] with [ALPHA], then `if < 0 then 0`,
  `if > 1 then 1`: these comparisons clip `±∞` but not NaN, so finiteness of the filter output
  comes first. `takeover` sets it to `_throttle_in` once.
- `_throttle_out`: `output_armed_stabilizing`, `(best_rpy + thr_adj) / compensation_gain` — [DIV]
  (`lift_max = 1` every tick, density ratio constrained to `[0.5, 1.25]`, gain in `[0.8, 2]`).
- `_thrust_rpyt_out`: `output_armed_stabilizing`, `rp · factor + yaw · factor` rescaled by
  `rpy_scale ≤ 1` — [LIN]/[DIV]; overwritten before it is read each tick.
- `_dt_s`: a copy of `last_loop_time_s`. `_disarm_safe_timer`: `t + dt` below `MOT_SAFE_TIME`,
  else the parameter — bounded accumulator `≤ MOT_SAFE_TIME + dtmax`.
- `_thrust_boost_ratio`: `MAX 0 (r - dt/spool_time)`, spool time `≥ 0.05` — [MINMAX] with finite `dt`.
- Free: `_actuator` (this file), `_throttle_avg_max` (clip), `_throttle_filter_cutoff`,
  `_throttle_thrust_max`, `_spin_up_ratio`, `_throttle_limit`, `thr_lin.*` (literals),
  `_throttle_hover`, `air_density_ratio` (parameters), motor factors (init only, `cos` of
  constants: [TRIG] on concrete values).

### AC_AttitudeControl, AC_AttitudeControl_Multi (`AC_AttitudeControl/*.lean`)
- `_attitude_target` (quaternion): `update_attitude_target` (product with
  `from_axis_angle(ω·dt)`, then `normalize`), `attitude_controller_run_quat` (may be replaced by
  `q_body · correction · heading`, not normalized), the non-feedforward branches — [QUAT].
- `_ang_vel_target_rads`: `attitude_command_model`, `v + a·dt` — [FBINT] + [SHAPE]. Roll and
  pitch are unlimited at the default `ATC_RATE_R_MAX = ATC_RATE_P_MAX = 0`; yaw is clipped to
  `ATC_RATE_WPY_MAX`. The hardest field; everything downstream inherits its bound.
- `_ang_accel_target_rads`: `shape_angle_vel_accel`, target clipped to `±accel_max` — [SHAPE]
  (needs `wrap_PI` finite on finite input).
- `_ang_vel_body_rads`: `ang_vel_limit(sqrt_controller(err)) + R · ang_vel_target` (+ gyro blend) —
  `sqrt_controller` bounded since `|err| ≤ π(1+u)` after `wrap_PI`, plus [QUAT] and [FBINT];
  needs `ATC_ANG_*_P` finite.
- `_euler_angle_target_rad`, `_thrust_angle_rad`, `_thrust_error_angle_rad`,
  `_feedforward_scalar`: `to_euler_vec`, `acos (constrain ...)` — [TRIG].
- `_euler_rate_target_rads`: `body_to_euler_derivative`, division by `cos pitch` guarded by
  `FLT_EPSILON` — [DIV]; written, never read on the path. `_attitude_ang_error`: `q_body⁻¹ q_target`
  — [QUAT]; written, never read.
- `_throttle_in`: `-thrust_d_norm` from `AC_PosControl` — [LIN].
- `_althold_lean_angle_max_rad`: `update_althold_lean_angle_max`,
  `x + (dt/(dt + ATC_ANG_LIM_TC)) · (acos(constrain ...) - x)` — [LPF] with a gain that is not
  [ALPHA]: needs the parameter hypothesis `ATC_ANG_LIM_TC > 0` (with `tc = 0` and a `dt_us = 0`
  tick the gain is `0/0 = NaN`; with `tc < 0` it leaves `[0,1]`). The one NaN source at finite
  inputs found.
- Free: `_dt_s`, `_rate_gyro_rads` (copies), `_throttle_rpy_mix` (clip), `_angle_boost` (clip),
  `_throttle_rpy_mix_desired`, `_rate_rp_tc`, `_rate_y_tc`, `_pd_scale`, `_i_scale`,
  `_angle_P_scale` and their `_used` copies, `_sysid_*` (literals and parameters).

### AC_PID, AC_PID_Basic, AC_PID_2D, AC_P_1D, AC_P_2D (`AC_PID/*.lean`)
Instances: rate roll, pitch, yaw (`AC_PID`); `_pid_accel_d_m` (`AC_PID`); `_pid_vel_d_m`
(`AC_PID_Basic`); `_pid_vel_ne_m` (`AC_PID_2D`); `_p_pos_d_m` (`AC_P_1D`); `_p_pos_ne_m` (`AC_P_2D`).
- `AC_PID._target`, `_error`: [LPF] with [ALPHA] (`FLTT`, `FLTE`) of the target and of
  `target - measurement` (bounds `B`, `2B`); `_pid_accel_d_m` has `FLTT = 0`, a copy.
- `AC_PID._derivative`: [DQ] then [LPF] (`FLTD`). `_target_derivative`: [DQ].
- `AC_PID._pid_info.*`: products of the above — [LIN]; only `FF`, `DFF` are read (`get_ff`).
- `AC_PID_Basic._target` (copy), `_error` ([LPF]), `_derivative` ([DQ] + [LPF]), `_pid_info.*`
  ([LIN], logging only).
- `AC_PID_2D._target` (copy), `_error` ([LPF]), `_derivative` ([DQ] + [LPF]), `_integrator`
  (`limit_length` to `IMAX`: [LIMLEN], needs the increment `e·I·dt` finite), `_pid_info_x/_y`
  ([LIN], logging only).
- `AC_P_1D._error`: `tofloat(target - meas)` then a comparison clamp to `[_error_min, _error_max]`
  — [NARROW] (the clamp lets NaN through). `AC_P_2D._error`: `tofloat` of the difference then
  `limit_length` — [NARROW] + [LIMLEN].
- Free: `AC_PID._integrator`, `AC_PID_Basic._integrator` (`constrain_float` to `±IMAX`; any finite
  `IMAX`, by the unordered-bounds argument of `constrain_unit` generalized from `[0, 1]`), the `P_1D`/`P_2D` limits (event writes
  from parameters, [DIV] with `FLT_EPSILON` guards).

### AC_PosControl (`AC_AttitudeControl/AC_PosControl.lean`)
- `_pos_target_ned_m`, `_pos_desired_ned_m` (`Float`): desired + offset (+ terrain), rewritten by
  the `P_1D`/`P_2D` errors; the path samples `origin + unit · s` per leg — [LIN] in the waypoint
  and estimate bounds.
- `_vel_desired_ned_ms`, `_accel_desired_ned_mss`: from `AC_WPNav`, `unit · V1 · vel_dt_scalar`
  with `vel_dt_scalar = _offset_vel_ms / _wp_desired_speed` — [LIN] + [DIV] (speed `≥ 0.01`) +
  [FBINT] via `_offset_vel_ms`.
- `_vel_target_ned_ms`: `sqrt_controller(P error) + vel_desired + offset` — [LIN].
- `_accel_target_ned_mss.xy`: PID output + feedforward, `limit_accel_xy` to
  `g · tan(min(althold, lean_max))` — [LIMLEN] + [TRIG]. `.z`: PID output · scaler + feedforward,
  unclamped — [LIN].
- `_limit_vector_ned.xy`: a copy of the pre-limit acceleration — [LIN].
- `_yaw_target_rad`: `atan2` of the desired velocity — [TRIG]. `_yaw_rate_target_rads`:
  `|accel_turn| / |vel_des|` stored only when `|vel_des| > 0.05 · _vel_max_ne_ms` — [DIV].
- `_pos_terrain_d_m`, `_vel_terrain_d_ms`, `_accel_terrain_d_mss`, all `_pos/_vel/_accel_offset_*`
  (target and current, NE and D): `update_terrain`, `NE/D_update_offsets` — [ZERO]
  (`set_posvelaccel_offset_target_*` is never called), otherwise genuine [FBINT] accumulators.
- `_roll_target_rad`, `_pitch_target_rad`: `atan` — [TRIG]; written, never read.
- Free: `_dt_s`, `_pos_estimate_ned_m`, `_vel_estimate_ned_ms` (copies), `_vel_d_control_ratio`
  (clip), `_pid_accel_d_m_kimax`, speed/acceleration/jerk limits, `_angle_max_override_rad`,
  `_pos_terrain_target_d_m`, `_ne_control_scale_factor` (parameters and literals).

### AC_WPNav and SimplePath (`AC_WPNav/*.lean`)
- `_offset_vel_ms`: `update_vel_accel` with limit 0 (`v + a·dt`), rescaled by `speed · v /
  desired` on a speed change — [FBINT] + [DIV].
- `_offset_accel_mss`: `shape_vel_accel` with `limit_total`, `±WP_ACC` — [SHAPE].
- `_track_dt_scalar`: `x + (t - x) · (dt / (WP_ACC / _wp_jerk_msss))`, `t ∈ [0,1]` clipped —
  [LPF] with a gain that is not [ALPHA]: needs `dt ≤ WP_ACC / WP_JERK` (gain in `[0,1]`; `(1,2)`
  still contracts, `≥ 2` diverges).
- `_origin_ned_m` (`Float`), when set to the stopping point `estimate + vel · (dist/speed)` —
  [DIV]; otherwise a waypoint copy.
- `SimplePath.time`: `MIN (time + dt') t_end` — [MINMAX]; the lower bound needs `dt' ≥ 0`, which
  fails if `_offset_vel_ms` or `_track_dt_scalar` overshoots below 0 (else [FBINT] horizon).
- `SimplePath.seg_delta`, `seg_length`: `tofloat(dest - origin)`, `length` — [NARROW] and
  `|delta| ≤ 1.8e19` so that the squared length is finite.
- `SimplePath.vel_max`, `accel_max`: `kinematic_limit` — [DIV] (normalized direction components
  chosen by the slope test), needs `WP_SPD*`, `WP_ACC*` finite.
- `SimplePath.vel_peak`, `t_accel_end`, `t_decel_start`, `t_end`: `generate_profile`, `v²/(2a)`,
  `v/a`, `(L - 2d)/v`, `safe_sqrt(L·a)` — [DIV] with `a, v ≥ FLT_EPSILON`.
- Free: `_wp_speed_ms`, `_wp_radius_m`, `_wp_jerk_msss`, `_wp_desired_speed_ne_ms`,
  `_last_wp_speed_*`, `_scurve_*`, `_destination_ned_m`, `_next_destination_ned_m`,
  `SimplePath.accel_z_max` (parameters, `MAX` with constants, waypoint copies).

### The hard cases, in order
1. The unclamped feedback integrators `_ang_vel_target_rads` (at the default unlimited rates) and
   `_offset_vel_ms` ([FBINT]); everything downstream inherits their bound.
2. The two filters whose gain is not [ALPHA]: `_althold_lean_angle_max_rad` (needs
   `ATC_ANG_LIM_TC > 0`) and `_track_dt_scalar` (needs `dt ≤ WP_ACC / WP_JERK`).
3. The difference quotients [DQ]: finite only through the `dt ≥ 1e-6` granularity.
4. Comparison-only clamps (`_throttle_filter_value`, `AC_P_1D._error`) and `MAX 0 x` do not catch
   NaN; their arguments must be shown finite first.
5. `limit_length` on a vector with an infinite component gives NaN ([LIMLEN]).
6. Quaternion norms scale with `‖q_sample‖` ([QUAT]).
7. [ZERO] for the `AC_PosControl` offset and terrain accumulators, as an invariant of reachable
   states.
-/

end Contracts.CopterCode
