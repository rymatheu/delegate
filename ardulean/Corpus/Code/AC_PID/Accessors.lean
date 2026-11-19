import ArduLean.Vehicle
import Corpus.Machine.Int

/-!
# AC_PID: the accessors of `AC_PID.h`, `AC_PID_2D.h`, `AC_PID_Basic.h`, `AC_P.h`, `AC_P_1D.h`, `AC_P_2D.h`

Each accessor returns the address of a parameter or member (`this + k`); `kP` is the object's first field.
-/

open FloatLib.Floats (Binary32 Binary64)

set_option linter.dupNamespace false

namespace Corpus.AC_PID

/-- C++ `AC_PID::kP : AP_Float &()`, `AP_Common.h:97-?`. -/
theorem AC_PID.kP_eq (this : UInt64) :
    Vehicle_lib.AC_PID.kP this = pure (Vehicle_lib.AC_PID.kP.pure' this) := rfl

/-- Case: the address of the object itself (the value or member is its first field). -/
theorem AC_PID.kP_pure_eq (this : UInt64) : Id.run (Vehicle_lib.AC_PID.kP.pure' this) = this := rfl

/-- C++ `AC_PID::ff : AP_Float &()`, `AP_Common.h:102-?`. -/
theorem AC_PID.ff_eq (this : UInt64) :
    Vehicle_lib.AC_PID.ff this = pure (Vehicle_lib.AC_PID.ff.pure' this) := rfl

/-- Case: the member's address `this + 12`. -/
theorem AC_PID.ff_pure_eq (this : UInt64) : Id.run (Vehicle_lib.AC_PID.ff.pure' this) = this + 12 := rfl

/-- Meaning: the address `this + 12` as a number, when it does not wrap. -/
theorem AC_PID.ff_toNat {this : UInt64} (h : this.toNat + 12 < 2 ^ 64) :
    (Id.run (Vehicle_lib.AC_PID.ff.pure' this)).toNat = this.toNat + 12 :=
  Corpus.Int.toNat_add_of_lt h

/-- C++ `AC_PID::filt_T_hz : AP_Float &()`, `AP_Common.h:103-?`. -/
theorem AC_PID.filt_T_hz_eq (this : UInt64) :
    Vehicle_lib.AC_PID.filt_T_hz this = pure (Vehicle_lib.AC_PID.filt_T_hz.pure' this) := rfl

/-- Case: the member's address `this + 24`. -/
theorem AC_PID.filt_T_hz_pure_eq (this : UInt64) : Id.run (Vehicle_lib.AC_PID.filt_T_hz.pure' this) = this + 24 := rfl

/-- Meaning: the address `this + 24` as a number, when it does not wrap. -/
theorem AC_PID.filt_T_hz_toNat {this : UInt64} (h : this.toNat + 24 < 2 ^ 64) :
    (Id.run (Vehicle_lib.AC_PID.filt_T_hz.pure' this)).toNat = this.toNat + 24 :=
  Corpus.Int.toNat_add_of_lt h

/-- C++ `AC_PID::filt_E_hz : AP_Float &()`, `AP_Common.h:104-?`. -/
theorem AC_PID.filt_E_hz_eq (this : UInt64) :
    Vehicle_lib.AC_PID.filt_E_hz this = pure (Vehicle_lib.AC_PID.filt_E_hz.pure' this) := rfl

/-- Case: the member's address `this + 28`. -/
theorem AC_PID.filt_E_hz_pure_eq (this : UInt64) : Id.run (Vehicle_lib.AC_PID.filt_E_hz.pure' this) = this + 28 := rfl

/-- Meaning: the address `this + 28` as a number, when it does not wrap. -/
theorem AC_PID.filt_E_hz_toNat {this : UInt64} (h : this.toNat + 28 < 2 ^ 64) :
    (Id.run (Vehicle_lib.AC_PID.filt_E_hz.pure' this)).toNat = this.toNat + 28 :=
  Corpus.Int.toNat_add_of_lt h

/-- C++ `AC_PID_2D::ff : AP_Float &()`, `AP_Common.h:53-?`. -/
theorem AC_PID_2D.ff_eq (this : UInt64) :
    Vehicle_lib.AC_PID_2D.ff this = pure (Vehicle_lib.AC_PID_2D.ff.pure' this) := rfl

/-- Case: the member's address `this + 12`. -/
theorem AC_PID_2D.ff_pure_eq (this : UInt64) : Id.run (Vehicle_lib.AC_PID_2D.ff.pure' this) = this + 12 := rfl

/-- Meaning: the address `this + 12` as a number, when it does not wrap. -/
theorem AC_PID_2D.ff_toNat {this : UInt64} (h : this.toNat + 12 < 2 ^ 64) :
    (Id.run (Vehicle_lib.AC_PID_2D.ff.pure' this)).toNat = this.toNat + 12 :=
  Corpus.Int.toNat_add_of_lt h

/-- C++ `AC_P_1D::kP : AP_Float &()`, `AC_P_1D.h:42-?`. -/
theorem AC_P_1D.kP_eq (this : UInt64) :
    Vehicle_lib.AC_P_1D.kP this = pure (Vehicle_lib.AC_P_1D.kP.pure' this) := rfl

/-- Case: the address of the object itself (the value or member is its first field). -/
theorem AC_P_1D.kP_pure_eq (this : UInt64) : Id.run (Vehicle_lib.AC_P_1D.kP.pure' this) = this := rfl

/-- C++ `AC_P_2D::kP : AP_Float &()`, `AC_P_2D.h:39-?`. -/
theorem AC_P_2D.kP_eq (this : UInt64) :
    Vehicle_lib.AC_P_2D.kP this = pure (Vehicle_lib.AC_P_2D.kP.pure' this) := rfl

/-- Case: the address of the object itself (the value or member is its first field). -/
theorem AC_P_2D.kP_pure_eq (this : UInt64) : Id.run (Vehicle_lib.AC_P_2D.kP.pure' this) = this := rfl

/-- C++ `AC_PID_Basic::kP : AP_Float &()`, `AP_Common.h:47-?`. -/
theorem AC_PID_Basic.kP_eq (this : UInt64) :
    Vehicle_lib.AC_PID_Basic.kP this = pure (Vehicle_lib.AC_PID_Basic.kP.pure' this) := rfl

/-- Case: the address of the object itself (the value or member is its first field). -/
theorem AC_PID_Basic.kP_pure_eq (this : UInt64) : Id.run (Vehicle_lib.AC_PID_Basic.kP.pure' this) = this := rfl

/-- C++ `AC_PID::kI : AP_Float &()`, `AP_Common.h:98-?`. -/
theorem AC_PID.kI_eq (this : UInt64) :
    Vehicle_lib.AC_PID.kI this = pure (Vehicle_lib.AC_PID.kI.pure' this) := rfl

/-- Case: the member's address `this + 4`. -/
theorem AC_PID.kI_pure_eq (this : UInt64) : Id.run (Vehicle_lib.AC_PID.kI.pure' this) = this + 4 := rfl

/-- Meaning: the address `this + 4` as a number, when it does not wrap. -/
theorem AC_PID.kI_toNat {this : UInt64} (h : this.toNat + 4 < 2 ^ 64) :
    (Id.run (Vehicle_lib.AC_PID.kI.pure' this)).toNat = this.toNat + 4 :=
  Corpus.Int.toNat_add_of_lt h

/-- C++ `AC_P::kP : AP_Float &()`, `AP_Common.h:51-?`. -/
theorem AC_P.kP_eq (this : UInt64) :
    Vehicle_lib.AC_P.kP this = pure (Vehicle_lib.AC_P.kP.pure' this) := rfl

/-- Case: the address of the object itself (the value or member is its first field). -/
theorem AC_P.kP_pure_eq (this : UInt64) : Id.run (Vehicle_lib.AC_P.kP.pure' this) = this := rfl

/-- C++ `AC_PID::kD : AP_Float &()`, `AP_Common.h:99-?`. -/
theorem AC_PID.kD_eq (this : UInt64) :
    Vehicle_lib.AC_PID.kD this = pure (Vehicle_lib.AC_PID.kD.pure' this) := rfl

/-- Case: the member's address `this + 8`. -/
theorem AC_PID.kD_pure_eq (this : UInt64) : Id.run (Vehicle_lib.AC_PID.kD.pure' this) = this + 8 := rfl

/-- Meaning: the address `this + 8` as a number, when it does not wrap. -/
theorem AC_PID.kD_toNat {this : UInt64} (h : this.toNat + 8 < 2 ^ 64) :
    (Id.run (Vehicle_lib.AC_PID.kD.pure' this)).toNat = this.toNat + 8 :=
  Corpus.Int.toNat_add_of_lt h

/-- C++ `AC_PID::get_pid_info : const AP_PIDInfo &() const`, `AP_Common.h:149-?`. -/
theorem AC_PID.get_pid_info_eq (this : UInt64) :
    Vehicle_lib.AC_PID.get_pid_info this = pure (Vehicle_lib.AC_PID.get_pid_info.pure' this) := rfl

/-- Case: the member's address `this + 156`. -/
theorem AC_PID.get_pid_info_pure_eq (this : UInt64) : Id.run (Vehicle_lib.AC_PID.get_pid_info.pure' this) = this + 156 := rfl

/-- Meaning: the address `this + 156` as a number, when it does not wrap. -/
theorem AC_PID.get_pid_info_toNat {this : UInt64} (h : this.toNat + 156 < 2 ^ 64) :
    (Id.run (Vehicle_lib.AC_PID.get_pid_info.pure' this)).toNat = this.toNat + 156 :=
  Corpus.Int.toNat_add_of_lt h

/-- C++ `AC_P_2D::get_error : const Vector2f &() const`, `AP_Common.h:41-?`. -/
theorem AC_P_2D.get_error_eq (this : UInt64) :
    Vehicle_lib.AC_P_2D.get_error this = pure (Vehicle_lib.AC_P_2D.get_error.pure' this) := rfl

/-- Case: the member's address `this + 4`. -/
theorem AC_P_2D.get_error_pure_eq (this : UInt64) : Id.run (Vehicle_lib.AC_P_2D.get_error.pure' this) = this + 4 := rfl

/-- Meaning: the address `this + 4` as a number, when it does not wrap. -/
theorem AC_P_2D.get_error_toNat {this : UInt64} (h : this.toNat + 4 < 2 ^ 64) :
    (Id.run (Vehicle_lib.AC_P_2D.get_error.pure' this)).toNat = this.toNat + 4 :=
  Corpus.Int.toNat_add_of_lt h

/-- C++ `AC_PID_2D::get_error : const Vector2f &() const`, `AP_Common.h:38-?`. -/
theorem AC_PID_2D.get_error_eq (this : UInt64) :
    Vehicle_lib.AC_PID_2D.get_error this = pure (Vehicle_lib.AC_PID_2D.get_error.pure' this) := rfl

/-- Case: the member's address `this + 36`. -/
theorem AC_PID_2D.get_error_pure_eq (this : UInt64) : Id.run (Vehicle_lib.AC_PID_2D.get_error.pure' this) = this + 36 := rfl

/-- Meaning: the address `this + 36` as a number, when it does not wrap. -/
theorem AC_PID_2D.get_error_toNat {this : UInt64} (h : this.toNat + 36 < 2 ^ 64) :
    (Id.run (Vehicle_lib.AC_PID_2D.get_error.pure' this)).toNat = this.toNat + 36 :=
  Corpus.Int.toNat_add_of_lt h

/-- C++ `AC_PID_2D::kP : AP_Float &()`, `AP_Common.h:50-?`. -/
theorem AC_PID_2D.kP_eq (this : UInt64) :
    Vehicle_lib.AC_PID_2D.kP this = pure (Vehicle_lib.AC_PID_2D.kP.pure' this) := rfl

/-- Case: the address of the object itself (the value or member is its first field). -/
theorem AC_PID_2D.kP_pure_eq (this : UInt64) : Id.run (Vehicle_lib.AC_PID_2D.kP.pure' this) = this := rfl

end Corpus.AC_PID
