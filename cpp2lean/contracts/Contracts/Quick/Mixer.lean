import FloatModel.Lit
import Contracts.Quick.Order

/-!
# Q1: what the rate controller hands the mixer, and the mixer's throttle clamps

`Q1 rate_outputs_bounded` as posed (roll, pitch, yaw in `[-1, 1]` and throttle in `[0, 1]` for every
input) is **false**: no clamp exists between the rate PIDs (`AC_PID::update_all`, output
`P + D + I`) and the mixer's inputs `_roll_in`, `_pitch_in`, `_yaw_in` (`AP_Motors::set_roll` etc.
store the value unchanged), nor between `AC_PosControl::D_update_controller` and `_throttle_in`
(counterexamples in `QUICK.md`, evaluated by `quick_cex`). What the translated code does clamp:

* `rate_controller_nonfinite`: a non-finite gyro sample on an axis gives the mixer `0 + sysid` on
  that axis (`rate_pid_nonfinite`: the entry guard of `AC_PID::update_all`);
* `set_throttle_avg_max_unit01`: the mixer's throttle limit `_throttle_avg_max` is finite and in
  `[0, 1]` for every input, NaN included (`AP_Motors::set_throttle_avg_max`,
  `constrain_value(…, 0, 1)`);
* `update_throttle_filter_out`: the mixer's throttle `get_throttle()` (the filtered throttle) is NaN
  or finite and in `[0, 1]` after `AP_MotorsMulticopter::update_throttle_filter`, which is the first
  step of every `AP_MotorsMulticopter::output`; NaN passes its two comparisons (`< 0`, `> 1`), so the
  precise statement is the disjunction. It is NaN exactly when the low-pass filter output is NaN
  (for instance after a NaN `_throttle_in`).

Q7: none of these depends on the period: they hold for every `_dt_s` and every input value.
-/

open Std.Do Vehicle

namespace Contracts.Quick

set_option linter.unusedSimpArgs false
set_option linter.deprecated.syntax false

def Unit01 (a : Float32) : Prop := a.IsFinite ∧ 0 ≤ a.toReal ∧ a.toReal ≤ 1

theorem unit01_zero : Unit01 (0.0 : Float32) :=
  ⟨Float32.isFinite_lit_zero, by simp, by simp⟩
theorem unit01_one : Unit01 (1.0 : Float32) :=
  ⟨Float32.isFinite_lit_one, by simp, by simp⟩

/-- A float that is not below `0` and not above `1` is NaN or in `[0, 1]`. -/
theorem nan_or_unit01 {a : Float32} (h1 : ¬ a < 0.0) (h2 : ¬ a > 1.0) : a.isNaN = true ∨ Unit01 a := by
  rcases h : a.isNaN with _ | _
  · right
    obtain ⟨f, l, u⟩ := Float32.between_of_not_lt_of_not_gt h Float32.isFinite_lit_zero
      Float32.isFinite_lit_one h1 h2
    exact ⟨f, by simpa using l, by simpa using u⟩
  · left; rfl

theorem f32_one_lt_zero : ¬ ((1.0 : Float32) < 0.0) := by
  rw [Float32.lt_iff_toReal_lt Float32.isFinite_lit_one Float32.isFinite_lit_zero]; simp
theorem f32_one_lt_one : ¬ ((1.0 : Float32) < 1.0) := by
  rw [Float32.lt_iff_toReal_lt Float32.isFinite_lit_one Float32.isFinite_lit_one]; simp
theorem f32_zero_lt_zero : ¬ ((0.0 : Float32) < 0.0) := by
  rw [Float32.lt_iff_toReal_lt Float32.isFinite_lit_zero Float32.isFinite_lit_zero]; simp
theorem f32_one_lt_zero' : ¬ ((1.0 : Float32) < (0.0 : Float32)) := f32_one_lt_zero

set_option maxHeartbeats 4000000 in
theorem update_throttle_filter_out (s : AP_Motors_lib.AP_MotorsMatrix.State) inp :
    (AP_Motors_lib.AP_MotorsMatrix.update_throttle_filter s inp)._throttle_filter.output.isNaN = true ∨
      Unit01 (AP_Motors_lib.AP_MotorsMatrix.update_throttle_filter s inp)._throttle_filter.output := by
  generalize h : AP_Motors_lib.AP_MotorsMatrix.update_throttle_filter s inp = r
  apply Id.of_wp_run_eq h (fun r => r._throttle_filter.output.isNaN = true ∨ Unit01 r._throttle_filter.output)
  mvcgen
  all_goals simp_all +zetaDelta [AP_Motors_lib.LowPassFilterFloat.get,
    AP_Motors_lib.LowPassFilterFloat.reset_float, unit01_zero, unit01_one, f32_one_lt_zero,
    f32_one_lt_one, f32_zero_lt_zero, GT.gt]
  all_goals exact nan_or_unit01 (by assumption) (by assumption)

open AC_Attitude_lib in
/-- `AC_PID::update_all` (`AC_PID.cpp:196-311`) returns `0` and leaves its state alone when the
target or the measurement is not finite: the guard `if (!isfinite(target) || !isfinite(measurement))
return 0` at its entry. -/
theorem rate_pid_nonfinite (p : AC_PID.Params) (s : AC_PID.State) inp (target meas dt : Float32)
    (limit : Bool) (pd i : Float32) (h : target.isFinite = false ∨ meas.isFinite = false) :
    AC_PID.update_all p s inp target meas dt limit pd i = (s, 0.0) := by
  unfold AC_PID.update_all
  rcases h with h | h <;> simp [h]

open AC_Attitude_lib AC_AttitudeControl_Multi in
theorem sysid_update_throttle_gain_boost (p : Params) (s : State) inp :
    (update_throttle_gain_boost p s inp)._actuator_sysid = s._actuator_sysid := by
  unfold update_throttle_gain_boost set_PD_scale_mult set_angle_P_scale_mult
  simp only [id_run, id_pure]
  split <;> rfl

open AC_Attitude_lib AC_AttitudeControl_Multi in
theorem sysid_update_throttle_rpy_mix (s : State) inp :
    (update_throttle_rpy_mix s inp)._actuator_sysid = s._actuator_sysid := by
  unfold update_throttle_rpy_mix
  simp only [id_run, id_pure]
  split_ifs <;> rfl

open AC_Attitude_lib AC_AttitudeControl_Multi in
/-- **Q1, rate controller to mixer, non-finite gyro**: when the gyro sample of an axis is not
finite, the rate controller hands the mixer `0 + sysid` on that axis (the PID's entry guard),
whatever the other inputs; with the system-identification offset at `0` (as
`rate_controller_target_reset` leaves it at the end of every tick) that is `+0`. -/
theorem rate_controller_nonfinite (p : Params) (s : State) (o : Outputs) (inp : Inputs) :
    (inp.get_gyro_latest.x.isFinite = false →
      (rate_controller_run p s o inp).2.set_roll = 0.0 + s._actuator_sysid.x) ∧
    (inp.get_gyro_latest.y.isFinite = false →
      (rate_controller_run p s o inp).2.set_pitch = 0.0 + s._actuator_sysid.y) ∧
    (inp.get_gyro_latest.z.isFinite = false →
      (rate_controller_run p s o inp).2.set_yaw = 0.0 + s._actuator_sysid.z) := by
  have e1 := sysid_update_throttle_gain_boost p s inp
  have e2 := sysid_update_throttle_rpy_mix (update_throttle_gain_boost p s inp) inp
  unfold rate_controller_run rate_controller_run_dt
  simp only [id_run, id_pure]
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rw [rate_pid_nonfinite _ _ _ _ _ _ _ _ _ (Or.inr h)]; simp only [e2, e1]
  · rw [rate_pid_nonfinite _ _ _ _ _ _ _ _ _ (Or.inr h)]; simp only [e2, e1]
  · rw [rate_pid_nonfinite _ _ _ _ _ _ _ _ _ (Or.inr h)]; simp only [e2, e1]

theorem set_throttle_avg_max_unit01 (ms : AP_Motors_lib.AP_MotorsMatrix.State) (v : Float32) :
    Unit01 (AP_Motors_lib.AP_MotorsMatrix.set_throttle_avg_max ms v)._throttle_avg_max := by
  have hm : (1 : ℝ) ≤ Float.Model.UnpackedFloat.maxFinite32 / 2 := by
    rw [Float.Model.UnpackedFloat.maxFinite32]; norm_num
  have e : (AP_Motors_lib.AP_MotorsMatrix.set_throttle_avg_max ms v)._throttle_avg_max =
      Float32.cvl v 0.0 1.0 := rfl
  rw [e]
  obtain ⟨h1, h2, h3⟩ := Float32.cvl_mem Float32.two32 (amt := v) (A := 0) (B := 1)
    Float32.isFinite_lit_zero Float32.isFinite_lit_one
    (by simp; linarith) (by simp; linarith) (by simp) (by simp) (by simp) (by simp)
  exact ⟨h1, h2, h3⟩

end Contracts.Quick
