import ArduLean.Vehicle
import Corpus.Machine.Int
import Corpus.Machine.Float

/-!
# AP_BattMonitor: `AP_BattMonitor.cpp`, `AP_BattMonitor_Backend.h`

The cell-voltage record lookup (an out-of-range instance falls back to instance 0), the charge increment, and the
backend's constant answers.
-/

open FloatLib.Floats (Binary32 Binary64)

set_option linter.dupNamespace false

namespace Corpus.AP_BattMonitor

/-! ## `AP_BattMonitor.cpp`, `AP_BattMonitor_Backend.h` -/

theorem AP_BattMonitor.get_cell_voltages_eq (this : UInt64) (i : UInt8) :
    Vehicle_lib.AP_BattMonitor.get_cell_voltages this i = pure (Vehicle_lib.AP_BattMonitor.get_cell_voltages.pure' this i) :=
  rfl

/-- Meaning: the cell record of instance `i` (112 bytes each, from `this + 408`); an instance from 9 on gives
instance 0's (`AP_BattMonitor.cpp:1030-1037`). -/
theorem AP_BattMonitor.get_cell_voltages_toNat (this : UInt64) (i : UInt8) :
    (Id.run (Vehicle_lib.AP_BattMonitor.get_cell_voltages.pure' this i)).toNat =
      (this.toNat + 408 + 112 * (if 9 ≤ i.toNat then 0 else i.toNat)) % 2 ^ 64 := by
  have m : ∀ c : UInt8, ((c.toUInt64.toInt64 * 112).toUInt64).toNat = 112 * c.toNat := by decide +kernel
  have z : ((Int32.toInt64 0 * 112).toUInt64).toNat = 0 := by decide
  have e := Corpus.Int.toInt_u8 i
  unfold Vehicle_lib.AP_BattMonitor.get_cell_voltages.pure'
  simp only [Id.run, ge_iff_le, decide_eq_true_eq, Int32.le_iff_toInt_le, e]
  have k : (9 : Int32).toInt = 9 := by decide
  rw [k]
  split_ifs with h1 h2 h2
  · show ((this + 408) + ((Int32.toInt64 0 * 112).toUInt64)).toNat = _
    rw [UInt64.toNat_add, UInt64.toNat_add, z]; simp <;> omega
  · omega
  · omega
  · show ((this + 408) + ((i.toUInt64.toInt64 * 112).toUInt64)).toNat = _
    rw [UInt64.toNat_add, UInt64.toNat_add, m]; simp <;> omega

theorem AP_BattMonitor_Backend.calculate_mah_eq (amps dt : Binary32) :
    Vehicle_lib.AP_BattMonitor_Backend.calculate_mah amps dt =
      pure (Vehicle_lib.AP_BattMonitor_Backend.calculate_mah.pure' amps dt) := rfl

/-- Case: `amps · dt_us` scaled by `1/3.6e9` (the word `0x3495248b`, `AP_BattMonitor_Backend.h`). -/
theorem AP_BattMonitor_Backend.calculate_mah_pure_eq (amps dt : Binary32) :
    Id.run (Vehicle_lib.AP_BattMonitor_Backend.calculate_mah.pure' amps dt) =
      (amps * dt) * Binary32.ofBits 0x3495248b := rfl

/-- NaN: a NaN current or interval gives a NaN charge. -/
theorem AP_BattMonitor_Backend.calculate_mah_of_isNaN {amps dt : Binary32}
    (h : Binary32.isNaN amps = true ∨ Binary32.isNaN dt = true) :
    Binary32.isNaN (Id.run (Vehicle_lib.AP_BattMonitor_Backend.calculate_mah.pure' amps dt)) = true := by
  rw [AP_BattMonitor_Backend.calculate_mah_pure_eq]
  exact Corpus.F32.isNaN_mul_of_isNaN (Or.inl (Corpus.F32.isNaN_mul_of_isNaN h))

/-! ## Constant answers (`AP_BattMonitor_Backend.h`) -/

/-- C++ `AP_BattMonitor_Backend::has_temperature : bool () const`, `AP_BattMonitor_Backend.h:54-?`. -/
theorem AP_BattMonitor_Backend.has_temperature_eq (this : UInt64) :
    Vehicle_lib.AP_BattMonitor_Backend.has_temperature this = pure (Vehicle_lib.AP_BattMonitor_Backend.has_temperature.pure' this) := rfl

/-- Protocol: the constant answer. -/
theorem AP_BattMonitor_Backend.has_temperature_val (this : UInt64) : Id.run (Vehicle_lib.AP_BattMonitor_Backend.has_temperature.pure' this) = false := rfl

/-- C++ `AP_BattMonitor_Backend::has_cell_voltages : bool () const`, `AP_BattMonitor_Backend.h:51-?`. -/
theorem AP_BattMonitor_Backend.has_cell_voltages_eq (this : UInt64) :
    Vehicle_lib.AP_BattMonitor_Backend.has_cell_voltages this = pure (Vehicle_lib.AP_BattMonitor_Backend.has_cell_voltages.pure' this) := rfl

/-- Protocol: the constant answer. -/
theorem AP_BattMonitor_Backend.has_cell_voltages_val (this : UInt64) : Id.run (Vehicle_lib.AP_BattMonitor_Backend.has_cell_voltages.pure' this) = false := rfl

/-- C++ `AP_BattMonitor_Backend::get_mavlink_fault_bitmask : uint32_t () const`, `AP_Common.h:86-?`. -/
theorem AP_BattMonitor_Backend.get_mavlink_fault_bitmask_eq (this : UInt64) :
    Vehicle_lib.AP_BattMonitor_Backend.get_mavlink_fault_bitmask this = pure (Vehicle_lib.AP_BattMonitor_Backend.get_mavlink_fault_bitmask.pure' this) := rfl

/-- Protocol: the constant answer. -/
theorem AP_BattMonitor_Backend.get_mavlink_fault_bitmask_val (this : UInt64) : Id.run (Vehicle_lib.AP_BattMonitor_Backend.get_mavlink_fault_bitmask.pure' this) = 0 := rfl

end Corpus.AP_BattMonitor
