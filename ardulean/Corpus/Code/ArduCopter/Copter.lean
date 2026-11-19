import ArduLean.Vehicle
import Corpus.Machine.Int

/-!
# ArduCopter: the `Copter` class (`Copter.h`, `mode.cpp`, `system.cpp`, `sensors.cpp`) and `AP_Arming_Copter.cpp`

The mode table (`mode_from_mode_num`), the GCS member, and the constant answers of this build (no traditional
helicopter, no rangefinder interpolation, the object-avoidance and winch checks passing).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option linter.dupNamespace false

namespace Corpus.Copter

/-! ## `mode.cpp`: the mode object of a mode number -/

theorem Copter.mode_from_mode_num_eq (this : UInt64) (mode : UInt8) :
    Vehicle_lib.Copter.mode_from_mode_num this mode = pure (Vehicle_lib.Copter.mode_from_mode_num.pure' this mode) := rfl

/-- Protocol: the mode objects inside `Copter` (`mode.cpp:32-171`): STABILIZE (0), ALT_HOLD (2), AUTO (3), LOITER (5),
GUIDED (4), CIRCLE (7), LAND (9), RTL (6), BRAKE (17); any other number gives the null pointer. -/
theorem Copter.mode_from_mode_num_table (this : UInt64) (mode : UInt8) :
    Id.run (Vehicle_lib.Copter.mode_from_mode_num.pure' this mode) =
      if mode = 0 then this + 13096 else if mode = 2 then this + 11256 else if mode = 3 then this + 11368
      else if mode = 7 then this + 12400 else if mode = 5 then this + 12776 else if mode = 4 then this + 12520
      else if mode = 9 then this + 12640 else if mode = 6 then this + 12888 else if mode = 17 then this + 12280
      else 0 := by
  unfold Vehicle_lib.Copter.mode_from_mode_num.pure'
  simp only [Id.run, beq_iff_eq]
  split_ifs <;> rfl

/-- Safety: a mode number of the build gives a non-null mode object (when the object's offsets do not wrap). -/
theorem Copter.mode_from_mode_num_ne_zero {this : UInt64} {mode : UInt8} (ht : this.toNat + 13096 < 2 ^ 64)
    (hm : mode ∈ ([0, 2, 3, 4, 5, 6, 7, 9, 17] : List UInt8)) :
    Id.run (Vehicle_lib.Copter.mode_from_mode_num.pure' this mode) ≠ 0 := by
  rw [Copter.mode_from_mode_num_table]
  intro h0
  have := congrArg UInt64.toNat h0
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp only [UInt64.toNat_add, UInt64.reduceToNat, ite_true, ite_false, show (2 : UInt8) ≠ 0 by decide,
      reduceCtorEq] at this <;> simp at this <;> omega

/-! ## Accessors and constant answers (`Copter.h`, `system.cpp`, `sensors.cpp`, `AP_Arming_Copter.cpp`) -/

/-- C++ `Copter::gcs : GCS_Copter &()`, `Copter.h:341-?`. -/
theorem Copter.gcs_eq (this : UInt64) :
    Vehicle_lib.Copter.gcs this = pure (Vehicle_lib.Copter.gcs.pure' this) := rfl

/-- Case: the member's address `this + 8904`. -/
theorem Copter.gcs_pure_eq (this : UInt64) : Id.run (Vehicle_lib.Copter.gcs.pure' this) = this + 8904 := rfl

/-- Meaning: the address `this + 8904` as a number, when it does not wrap. -/
theorem Copter.gcs_toNat {this : UInt64} (h : this.toNat + 8904 < 2 ^ 64) :
    (Id.run (Vehicle_lib.Copter.gcs.pure' this)).toNat = this.toNat + 8904 :=
  Corpus.Int.toNat_add_of_lt h

/-- C++ `AP_Arming_Copter::oa_checks : bool (bool)`, `AP_Arming_Copter.cpp:319-336`. -/
theorem AP_Arming_Copter.oa_checks_eq (this : UInt64) (display_failure : Bool) :
    Vehicle_lib.AP_Arming_Copter.oa_checks this display_failure = pure (Vehicle_lib.AP_Arming_Copter.oa_checks.pure' this display_failure) := rfl

/-- Protocol: the constant answer. -/
theorem AP_Arming_Copter.oa_checks_val (this : UInt64) (display_failure : Bool) : Id.run (Vehicle_lib.AP_Arming_Copter.oa_checks.pure' this display_failure) = true := rfl

/-- C++ `AP_Arming_Copter::winch_checks : bool (bool) const`, `AP_Arming_Copter.cpp:529-548`. -/
theorem AP_Arming_Copter.winch_checks_eq (this : UInt64) (display_failure : Bool) :
    Vehicle_lib.AP_Arming_Copter.winch_checks this display_failure = pure (Vehicle_lib.AP_Arming_Copter.winch_checks.pure' this display_failure) := rfl

/-- Protocol: the constant answer. -/
theorem AP_Arming_Copter.winch_checks_val (this : UInt64) (display_failure : Bool) : Id.run (Vehicle_lib.AP_Arming_Copter.winch_checks.pure' this display_failure) = true := rfl

/-- C++ `Copter::is_tradheli : bool () const`, `system.cpp:567-574`. -/
theorem Copter.is_tradheli_eq (this : UInt64) :
    Vehicle_lib.Copter.is_tradheli this = pure (Vehicle_lib.Copter.is_tradheli.pure' this) := rfl

/-- Protocol: the constant answer. -/
theorem Copter.is_tradheli_val (this : UInt64) : Id.run (Vehicle_lib.Copter.is_tradheli.pure' this) = false := rfl

/-- C++ `Copter::get_rangefinder_height_interpolated_m : bool (float &) const`, `sensors.cpp:71-78`. -/
theorem Copter.get_rangefinder_height_interpolated_m_eq (this : UInt64) (height_m : UInt64) :
    Vehicle_lib.Copter.get_rangefinder_height_interpolated_m this height_m = pure (Vehicle_lib.Copter.get_rangefinder_height_interpolated_m.pure' this height_m) := rfl

/-- Protocol: the constant answer. -/
theorem Copter.get_rangefinder_height_interpolated_m_val (this : UInt64) (height_m : UInt64) : Id.run (Vehicle_lib.Copter.get_rangefinder_height_interpolated_m.pure' this height_m) = false := rfl

end Corpus.Copter

namespace Corpus.Copter

/-- C++ `Mode::gcs : GCS_Copter &() const`, `mode.cpp:1143-1146`: `copter.gcs()` of the global `copter` (`0x86d8`).
Case: the address `0x86d8 + 8904`. -/
theorem Mode.gcs_pure_eq (this : UInt64) : Id.run (Vehicle_lib.Mode.gcs.pure' this) = 0x86d8 + 8904 := rfl

/-- Order: `Mode::gcs` is `Copter::gcs` of the global `copter`. -/
theorem Mode.gcs_eq_copter_gcs (this : UInt64) :
    Id.run (Vehicle_lib.Mode.gcs.pure' this) = Id.run (Vehicle_lib.Copter.gcs.pure' 0x86d8) := rfl

/-- C++ `AP_Arming::method_is_GCS : bool (Method)`, `AP_Arming.h:172-174`. -/
theorem AP_Arming.method_is_GCS_eq (m : Int32) :
    Vehicle_lib.AP_Arming.method_is_GCS m = pure (Vehicle_lib.AP_Arming.method_is_GCS.pure' m) := rfl

/-- Protocol: the arming methods that count as the GCS's, numbered 1 and 35 in the code. -/
theorem AP_Arming.method_is_GCS_table (m : Int32) :
    Id.run (Vehicle_lib.AP_Arming.method_is_GCS.pure' m) = true ↔ m.toInt ∈ ([1, 35] : List Int) := by
  unfold Vehicle_lib.AP_Arming.method_is_GCS.pure'
  simp only [Id.run, pure, Bool.or_eq_true, beq_iff_eq, ← Int32.toInt_inj, Int32.toInt_ofNat, Int32.size,
    List.mem_cons, List.not_mem_nil, or_false]
  simp

end Corpus.Copter
