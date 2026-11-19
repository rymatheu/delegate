import ArduLean.Vehicle
import Corpus.Machine.Int

/-!
# SRV_Channel: `SRV_Channel.{h,cpp}`, `SRV_Channel_config.h`

The output-function tables: which functions are motors, which an emergency stop zeroes, the motor function of an
output channel, and the valid range.
-/

open FloatLib.Floats (Binary32 Binary64)

set_option linter.dupNamespace false

namespace Corpus.SRV_Channel

/-! ## Output functions (`SRV_Channel.{h,cpp}`, `SRV_Channel_config.h`) -/

theorem SRV_Channels.get_motor_function_eq (c : UInt8) :
    Vehicle_lib.SRV_Channels.get_motor_function c = pure (Vehicle_lib.SRV_Channels.get_motor_function.pure' c) := rfl

/-- Meaning: motor `c` (from 0) is `k_motor1 + c` (33…) for `c < 8`, `k_motor9 + (c - 8)` (82…) for `c < 12`, and
`k_motor13 + (c - 12)` (160…) beyond (`SRV_Channel_config.h:572-580`). -/
theorem SRV_Channels.get_motor_function_toInt (c : UInt8) :
    (Id.run (Vehicle_lib.SRV_Channels.get_motor_function.pure' c)).toInt =
      if c.toNat < 8 then 33 + c.toNat else if c.toNat < 12 then 74 + c.toNat else 148 + c.toNat := by
  revert c; unfold Vehicle_lib.SRV_Channels.get_motor_function.pure'; decide +kernel

/-- Order: the first eight motors are `is_motor`. -/
theorem SRV_Channels.get_motor_function_is_motor (c : UInt8) :
    Id.run (Vehicle_lib.SRV_Channel.is_motor.pure' (Id.run (Vehicle_lib.SRV_Channels.get_motor_function.pure' c))) =
      decide (c.toNat < 32) := by
  revert c; unfold Vehicle_lib.SRV_Channels.get_motor_function.pure' Vehicle_lib.SRV_Channel.is_motor.pure'
  decide +kernel

theorem SRV_Channel.valid_function_eq (fn : Int32) :
    Vehicle_lib.SRV_Channel.valid_function'2 fn = pure (Vehicle_lib.SRV_Channel.valid_function'2.pure' fn) := rfl

/-- Case: a function number is valid in `[0, 190)` (`SRV_Channel.h:232-234`). -/
theorem SRV_Channel.valid_function_iff (fn : Int32) :
    Id.run (Vehicle_lib.SRV_Channel.valid_function'2.pure' fn) = true ↔ 0 ≤ fn.toInt ∧ fn.toInt < 190 := by
  unfold Vehicle_lib.SRV_Channel.valid_function'2.pure'
  simp only [Id.run, pure, ge_iff_le, Bool.and_eq_true, decide_eq_true_eq, Int32.le_iff_toInt_le, Int32.lt_iff_toInt_lt,
    Int32.toInt_ofNat, Int32.size]
  simp

theorem SRV_Channel.is_motor_eq (fn : Int32) :
    Vehicle_lib.SRV_Channel.is_motor fn = pure (Vehicle_lib.SRV_Channel.is_motor.pure' fn) := rfl

/-- Case: the motor functions are `k_motor1…8` (33–40), `k_motor9…12` (82–85), `k_motor13…32` (160–179)
(`SRV_Channel.cpp:317-322`). -/
theorem SRV_Channel.is_motor_iff (fn : Int32) :
    Id.run (Vehicle_lib.SRV_Channel.is_motor.pure' fn) = true ↔
      (33 ≤ fn.toInt ∧ fn.toInt ≤ 40) ∨ (82 ≤ fn.toInt ∧ fn.toInt ≤ 85) ∨ (160 ≤ fn.toInt ∧ fn.toInt ≤ 179) := by
  unfold Vehicle_lib.SRV_Channel.is_motor.pure'
  simp only [Id.run, pure, ge_iff_le, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Int32.le_iff_toInt_le,
    Int32.toInt_ofNat, Int32.size]
  simp [or_assoc]

theorem SRV_Channel.should_e_stop_eq (fn : Int32) :
    Vehicle_lib.SRV_Channel.should_e_stop fn = pure (Vehicle_lib.SRV_Channel.should_e_stop.pure' fn) := rfl

/-- Protocol: the functions an emergency stop zeroes (`SRV_Channel.cpp:325-354`); the last disjunct is the source's
case range `k_motor13 ... k_motor32` (160–179). -/
theorem SRV_Channel.should_e_stop_table (fn : Int32) :
    Id.run (Vehicle_lib.SRV_Channel.should_e_stop.pure' fn) = true ↔
      fn.toInt ∈ ([31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 69, 70, 73, 74, 81, 82, 83, 84, 85, 30] : List Int) ∨
        (160 ≤ fn.toInt ∧ fn.toInt ≤ 179) := by
  unfold Vehicle_lib.SRV_Channel.should_e_stop.pure'
  simp only [Id.run, List.mem_cons, List.not_mem_nil, or_false]
  split <;> rename_i h <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, ← Int32.toInt_inj,
      Int32.le_iff_toInt_le, Int32.toInt_ofNat] at h <;>
    simp [Int32.size] at h <;>
    first
      | exact iff_of_true rfl (by omega)
      | exact iff_of_false Bool.false_ne_true (by omega)

/-- Protocol: an emergency stop zeroes every motor function, `k_motor1…32` (the defect of FINDINGS F20 is corrected in
the code). -/
theorem SRV_Channel.should_e_stop_of_is_motor {fn : Int32} (h : Id.run (Vehicle_lib.SRV_Channel.is_motor.pure' fn) = true) :
    Id.run (Vehicle_lib.SRV_Channel.should_e_stop.pure' fn) = true := by
  rw [SRV_Channel.is_motor_iff] at h
  rw [SRV_Channel.should_e_stop_table]
  simp only [List.mem_cons, List.not_mem_nil, or_false]
  omega

end Corpus.SRV_Channel
