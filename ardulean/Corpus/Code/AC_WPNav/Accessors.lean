import ArduLean.Vehicle
import Corpus.Machine.Int

/-!
# AC_WPNav: the accessors of `AC_WPNav.h`, `AC_Circle.h`

Member addresses (`this + k`).
-/

open FloatLib.Floats (Binary32 Binary64)

set_option linter.dupNamespace false

namespace Corpus.AC_WPNav

/-- C++ `AC_WPNav::get_wp_destination_NED_m : const Vector3p &() const`, `AC_WPNav.h:152-?`. -/
theorem AC_WPNav.get_wp_destination_NED_m_eq (this : UInt64) :
    Vehicle_lib.AC_WPNav.get_wp_destination_NED_m this = pure (Vehicle_lib.AC_WPNav.get_wp_destination_NED_m.pure' this) := rfl

/-- Case: the member's address `this + 2432`. -/
theorem AC_WPNav.get_wp_destination_NED_m_pure_eq (this : UInt64) : Id.run (Vehicle_lib.AC_WPNav.get_wp_destination_NED_m.pure' this) = this + 2432 := rfl

/-- Meaning: the address `this + 2432` as a number, when it does not wrap. -/
theorem AC_WPNav.get_wp_destination_NED_m_toNat {this : UInt64} (h : this.toNat + 2432 < 2 ^ 64) :
    (Id.run (Vehicle_lib.AC_WPNav.get_wp_destination_NED_m.pure' this)).toNat = this.toNat + 2432 :=
  Corpus.Int.toNat_add_of_lt h

/-- C++ `AC_Circle::get_center_NED_m : const Vector3p &() const`, `AC_Circle.h:47-?`. -/
theorem AC_Circle.get_center_NED_m_eq (this : UInt64) :
    Vehicle_lib.AC_Circle.get_center_NED_m this = pure (Vehicle_lib.AC_Circle.get_center_NED_m.pure' this) := rfl

/-- Case: the member's address `this + 32`. -/
theorem AC_Circle.get_center_NED_m_pure_eq (this : UInt64) : Id.run (Vehicle_lib.AC_Circle.get_center_NED_m.pure' this) = this + 32 := rfl

/-- Meaning: the address `this + 32` as a number, when it does not wrap. -/
theorem AC_Circle.get_center_NED_m_toNat {this : UInt64} (h : this.toNat + 32 < 2 ^ 64) :
    (Id.run (Vehicle_lib.AC_Circle.get_center_NED_m.pure' this)).toNat = this.toNat + 32 :=
  Corpus.Int.toNat_add_of_lt h

end Corpus.AC_WPNav
