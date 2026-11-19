import ArduLean.Vehicle
import Corpus.Machine.Int

/-!
# AP_Math: the accessors of `vector3.h`, `SCurve.h`, `SplineCurve.h`

Component and member addresses: `xy()` is the vector itself, `operator[]` is `this + 4·i`.
-/

open FloatLib.Floats (Binary32 Binary64)

set_option linter.dupNamespace false

namespace Corpus.AP_Math

/-- C++ `Vector3<float>::operator[] : const float &(uint8_t) const`, `vector3.h:144-150`. -/
theorem Vector3'float.operator___eq (this : UInt64) (i : UInt8) :
    Vehicle_lib.Vector3'float.operator__ this i = pure (Vehicle_lib.Vector3'float.operator__.pure' this i) := rfl

/-- Meaning: component `i` at `this + 4·i` (modulo `2^64`; no bounds check, as in C++). -/
theorem Vector3'float.operator___toNat (this : UInt64) (i : UInt8) :
    (Id.run (Vehicle_lib.Vector3'float.operator__.pure' this i)).toNat = (this.toNat + 4 * i.toNat) % 2 ^ 64 := by
  have m : ∀ c : UInt8, ((c.toUInt64.toInt64 * 4).toUInt64).toNat = 4 * c.toNat := by decide +kernel
  show (this + ((i.toUInt64.toInt64 * 4).toUInt64)).toNat = _
  rw [UInt64.toNat_add, m]

/-- C++ `Vector3<float>::xy : Vector2<float> &()`, `vector3.h:206-208`. -/
theorem Vector3'float.xy_eq (this : UInt64) :
    Vehicle_lib.Vector3'float.xy this = pure (Vehicle_lib.Vector3'float.xy.pure' this) := rfl

/-- Case: the address of the object itself (the value or member is its first field). -/
theorem Vector3'float.xy_pure_eq (this : UInt64) : Id.run (Vehicle_lib.Vector3'float.xy.pure' this) = this := rfl

/-- C++ `Vector3<double>::xy : Vector2<double> &()`, `vector3.h:206-208`. -/
theorem Vector3'double.xy_eq (this : UInt64) :
    Vehicle_lib.Vector3'double.xy this = pure (Vehicle_lib.Vector3'double.xy.pure' this) := rfl

/-- Case: the address of the object itself (the value or member is its first field). -/
theorem Vector3'double.xy_pure_eq (this : UInt64) : Id.run (Vehicle_lib.Vector3'double.xy.pure' this) = this := rfl

/-- C++ `SplineCurve::get_destination_vel : const Vector3f &()`, `AP_Common.h:27-?`. -/
theorem SplineCurve.get_destination_vel_eq (this : UInt64) :
    Vehicle_lib.SplineCurve.get_destination_vel this = pure (Vehicle_lib.SplineCurve.get_destination_vel.pure' this) := rfl

/-- Case: the member's address `this + 60`. -/
theorem SplineCurve.get_destination_vel_pure_eq (this : UInt64) : Id.run (Vehicle_lib.SplineCurve.get_destination_vel.pure' this) = this + 60 := rfl

/-- Meaning: the address `this + 60` as a number, when it does not wrap. -/
theorem SplineCurve.get_destination_vel_toNat {this : UInt64} (h : this.toNat + 60 < 2 ^ 64) :
    (Id.run (Vehicle_lib.SplineCurve.get_destination_vel.pure' this)).toNat = this.toNat + 60 :=
  Corpus.Int.toNat_add_of_lt h

/-- C++ `SCurve::get_origin_to_destination : const Vector3f &() const`, `AP_Common.h:98-?`. -/
theorem SCurve.get_origin_to_destination_eq (this : UInt64) :
    Vehicle_lib.SCurve.get_origin_to_destination this = pure (Vehicle_lib.SCurve.get_origin_to_destination.pure' this) := rfl

/-- Case: the member's address `this + 588`. -/
theorem SCurve.get_origin_to_destination_pure_eq (this : UInt64) : Id.run (Vehicle_lib.SCurve.get_origin_to_destination.pure' this) = this + 588 := rfl

/-- Meaning: the address `this + 588` as a number, when it does not wrap. -/
theorem SCurve.get_origin_to_destination_toNat {this : UInt64} (h : this.toNat + 588 < 2 ^ 64) :
    (Id.run (Vehicle_lib.SCurve.get_origin_to_destination.pure' this)).toNat = this.toNat + 588 :=
  Corpus.Int.toNat_add_of_lt h

end Corpus.AP_Math
