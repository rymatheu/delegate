import ArduLean.Vehicle
import Corpus.Machine.Memory
import Corpus.Machine.Hoare

/-!
# AP_Param: the `AP_Float` accessors (`AP_Param.h`)

`AP_ParamT<float, AP_PARAM_FLOAT>`'s conversion to `const float &` is the address of the parameter's value (the value
is the object's first field), and its unary minus loads the value and negates it.
-/

open FloatLib.Floats (Binary32 Binary64)

namespace Corpus.AP_Param

/-- C++ `AP_ParamT<float, 4>::operator const float & : const float &() const`, `AP_Param.h:1006-1008`. -/
theorem operator_const_float_eq (a : UInt64) :
    Vehicle_lib.AP_ParamT'float_4.operator_const_float__'1 a =
      pure (Vehicle_lib.AP_ParamT'float_4.operator_const_float__'1.pure' a) := rfl

theorem operator_const_float_pure_eq (a : UInt64) :
    Id.run (Vehicle_lib.AP_ParamT'float_4.operator_const_float__'1.pure' a) = a := rfl

theorem operator_const_float_run (a : UInt64) (s : PMem.Mem) :
    (Vehicle_lib.AP_ParamT'float_4.operator_const_float__'1 a).run s = (a, s) := rfl

/-- C++ `AP_ParamT<float, 4>::operator- : float () const`, `AP_Param.h:1022`: the negated value, the memory unchanged. -/
theorem operator_neg_run {a : UInt64} (hb : PMem.inBridgeN a 4 = false) (s : PMem.Mem) :
    (Vehicle_lib.AP_ParamT'float_4.operator_'3 a).run s =
      (-(Binary32.ofBits (Corpus.Mem.w32 s.m a.toNat)), s) := by
  unfold Vehicle_lib.AP_ParamT'float_4.operator_'3
  rw [StateT.run_bind, Corpus.Mem.ldF32_run hb]
  rfl

end Corpus.AP_Param

namespace Corpus.AP_Param

/-- `operator const float &` reads and writes nothing: every precondition is kept (third increment). -/
theorem operator_const_float_triple {P : PMem.Mem → Prop} (a : UInt64) :
    Corpus.Hoare.Triple P (Vehicle_lib.AP_ParamT'float_4.operator_const_float__'1 a) (fun _ => P) :=
  Corpus.Hoare.Triple.of_state fun s => congrArg Prod.snd (operator_const_float_run a s)

end Corpus.AP_Param

/-! ## The other parameter accessors (`AP_Param.h`) and `type_size` (`AP_Param.cpp`) (fourth increment)

`AP_ParamT<T, …>::operator const T &` and `AP_ParamTBase<T, …>::get` return the address of the value, the object's
first field. -/

namespace Corpus.AP_Param

set_option linter.dupNamespace false

theorem AP_Param.type_size_eq (t : UInt32) :
    Vehicle_lib.AP_Param.type_size t = pure (Vehicle_lib.AP_Param.type_size.pure' t) := rfl

/-- Protocol: the storage sizes (`AP_Param.cpp:702-721`): `AP_PARAM_INT8` 1, `INT16` 2, `INT32` and `FLOAT` 4,
`VECTOR3F` 12, `NONE`/`GROUP` and anything else 0. -/
theorem AP_Param.type_size_table :
    [(0, 0), (1, 1), (2, 2), (3, 4), (4, 4), (5, 12), (6, 0), (7, 0)].all
      (fun p : UInt32 × UInt8 => Id.run (Vehicle_lib.AP_Param.type_size.pure' p.1) == p.2) = true := by
  unfold Vehicle_lib.AP_Param.type_size.pure'; decide

/-- Range: at most 12 bytes. -/
theorem AP_Param.type_size_le (t : UInt32) : (Id.run (Vehicle_lib.AP_Param.type_size.pure' t)).toNat ≤ 12 := by
  unfold Vehicle_lib.AP_Param.type_size.pure'
  simp only [Id.run]
  split_ifs <;> decide

/-- C++ `AP_ParamTBase<signed char, 1>::get : const signed char &() const`, `AP_Param.h:917-919`. -/
theorem AP_ParamTBase'signed_char_1.get_eq (this : UInt64) :
    Vehicle_lib.AP_ParamTBase'signed_char_1.get this = pure (Vehicle_lib.AP_ParamTBase'signed_char_1.get.pure' this) := rfl

/-- Case: the address of the object itself (the value or member is its first field). -/
theorem AP_ParamTBase'signed_char_1.get_pure_eq (this : UInt64) : Id.run (Vehicle_lib.AP_ParamTBase'signed_char_1.get.pure' this) = this := rfl

/-- C++ `AP_ParamT<unsigned short, 2>::operator const unsigned short & : const unsigned short &() const`, `AP_Param.h:978-980`. -/
theorem AP_ParamT'unsigned_short_2.operator_const_unsigned_short___eq (this : UInt64) :
    Vehicle_lib.AP_ParamT'unsigned_short_2.operator_const_unsigned_short__ this = pure (Vehicle_lib.AP_ParamT'unsigned_short_2.operator_const_unsigned_short__.pure' this) := rfl

/-- Case: the address of the object itself (the value or member is its first field). -/
theorem AP_ParamT'unsigned_short_2.operator_const_unsigned_short___pure_eq (this : UInt64) : Id.run (Vehicle_lib.AP_ParamT'unsigned_short_2.operator_const_unsigned_short__.pure' this) = this := rfl

/-- C++ `AP_ParamV<Vector3<float>, 5>::get : const Vector3<float> &() const`, `AP_Param.h:1059-1061`. -/
theorem AP_ParamV'Vector3_float_5.get_eq (this : UInt64) :
    Vehicle_lib.AP_ParamV'Vector3_float_5.get this = pure (Vehicle_lib.AP_ParamV'Vector3_float_5.get.pure' this) := rfl

/-- Case: the address of the object itself (the value or member is its first field). -/
theorem AP_ParamV'Vector3_float_5.get_pure_eq (this : UInt64) : Id.run (Vehicle_lib.AP_ParamV'Vector3_float_5.get.pure' this) = this := rfl

/-- C++ `AP_ParamT<unsigned int, 3>::operator const unsigned int & : const unsigned int &() const`, `AP_Param.h:978-980`. -/
theorem AP_ParamT'unsigned_int_3.operator_const_unsigned_int___eq (this : UInt64) :
    Vehicle_lib.AP_ParamT'unsigned_int_3.operator_const_unsigned_int__ this = pure (Vehicle_lib.AP_ParamT'unsigned_int_3.operator_const_unsigned_int__.pure' this) := rfl

/-- Case: the address of the object itself (the value or member is its first field). -/
theorem AP_ParamT'unsigned_int_3.operator_const_unsigned_int___pure_eq (this : UInt64) : Id.run (Vehicle_lib.AP_ParamT'unsigned_int_3.operator_const_unsigned_int__.pure' this) = this := rfl

/-- C++ `AP_ParamT<short, 2>::operator const short & : const short &() const`, `AP_Param.h:978-980`. -/
theorem AP_ParamT'short_2.operator_const_short___eq (this : UInt64) :
    Vehicle_lib.AP_ParamT'short_2.operator_const_short__ this = pure (Vehicle_lib.AP_ParamT'short_2.operator_const_short__.pure' this) := rfl

/-- Case: the address of the object itself (the value or member is its first field). -/
theorem AP_ParamT'short_2.operator_const_short___pure_eq (this : UInt64) : Id.run (Vehicle_lib.AP_ParamT'short_2.operator_const_short__.pure' this) = this := rfl

/-- C++ `AP_ParamT<signed char, 1>::operator const signed char & : const signed char &() const`, `AP_Param.h:978-980`. -/
theorem AP_ParamT'signed_char_1.operator_const_signed_char___eq (this : UInt64) :
    Vehicle_lib.AP_ParamT'signed_char_1.operator_const_signed_char__ this = pure (Vehicle_lib.AP_ParamT'signed_char_1.operator_const_signed_char__.pure' this) := rfl

/-- Case: the address of the object itself (the value or member is its first field). -/
theorem AP_ParamT'signed_char_1.operator_const_signed_char___pure_eq (this : UInt64) : Id.run (Vehicle_lib.AP_ParamT'signed_char_1.operator_const_signed_char__.pure' this) = this := rfl

/-- C++ `AP_ParamTBase<float, 4>::get : const float &() const`, `AP_Param.h:917-919`. -/
theorem AP_ParamTBase'float_4.get_eq (this : UInt64) :
    Vehicle_lib.AP_ParamTBase'float_4.get this = pure (Vehicle_lib.AP_ParamTBase'float_4.get.pure' this) := rfl

/-- Case: the address of the object itself (the value or member is its first field). -/
theorem AP_ParamTBase'float_4.get_pure_eq (this : UInt64) : Id.run (Vehicle_lib.AP_ParamTBase'float_4.get.pure' this) = this := rfl

/-- C++ `AP_ParamTBase<unsigned int, 3>::get : const unsigned int &() const`, `AP_Param.h:917-919`. -/
theorem AP_ParamTBase'unsigned_int_3.get_eq (this : UInt64) :
    Vehicle_lib.AP_ParamTBase'unsigned_int_3.get this = pure (Vehicle_lib.AP_ParamTBase'unsigned_int_3.get.pure' this) := rfl

/-- Case: the address of the object itself (the value or member is its first field). -/
theorem AP_ParamTBase'unsigned_int_3.get_pure_eq (this : UInt64) : Id.run (Vehicle_lib.AP_ParamTBase'unsigned_int_3.get.pure' this) = this := rfl

/-- C++ `AP_ParamTBase<unsigned short, 2>::get : const unsigned short &() const`, `AP_Param.h:917-919`. -/
theorem AP_ParamTBase'unsigned_short_2.get_eq (this : UInt64) :
    Vehicle_lib.AP_ParamTBase'unsigned_short_2.get this = pure (Vehicle_lib.AP_ParamTBase'unsigned_short_2.get.pure' this) := rfl

/-- Case: the address of the object itself (the value or member is its first field). -/
theorem AP_ParamTBase'unsigned_short_2.get_pure_eq (this : UInt64) : Id.run (Vehicle_lib.AP_ParamTBase'unsigned_short_2.get.pure' this) = this := rfl

/-- C++ `AP_ParamT<unsigned char, 1>::operator const unsigned char & : const unsigned char &() const`, `AP_Param.h:978-980`. -/
theorem AP_ParamT'unsigned_char_1.operator_const_unsigned_char___eq (this : UInt64) :
    Vehicle_lib.AP_ParamT'unsigned_char_1.operator_const_unsigned_char__ this = pure (Vehicle_lib.AP_ParamT'unsigned_char_1.operator_const_unsigned_char__.pure' this) := rfl

/-- Case: the address of the object itself (the value or member is its first field). -/
theorem AP_ParamT'unsigned_char_1.operator_const_unsigned_char___pure_eq (this : UInt64) : Id.run (Vehicle_lib.AP_ParamT'unsigned_char_1.operator_const_unsigned_char__.pure' this) = this := rfl

/-- C++ `AP_ParamTBase<short, 2>::get : const short &() const`, `AP_Param.h:917-919`. -/
theorem AP_ParamTBase'short_2.get_eq (this : UInt64) :
    Vehicle_lib.AP_ParamTBase'short_2.get this = pure (Vehicle_lib.AP_ParamTBase'short_2.get.pure' this) := rfl

/-- Case: the address of the object itself (the value or member is its first field). -/
theorem AP_ParamTBase'short_2.get_pure_eq (this : UInt64) : Id.run (Vehicle_lib.AP_ParamTBase'short_2.get.pure' this) = this := rfl

/-- C++ `AP_ParamT<int, 3>::operator const int & : const int &() const`, `AP_Param.h:978-980`. -/
theorem AP_ParamT'int_3.operator_const_int___eq (this : UInt64) :
    Vehicle_lib.AP_ParamT'int_3.operator_const_int__ this = pure (Vehicle_lib.AP_ParamT'int_3.operator_const_int__.pure' this) := rfl

/-- Case: the address of the object itself (the value or member is its first field). -/
theorem AP_ParamT'int_3.operator_const_int___pure_eq (this : UInt64) : Id.run (Vehicle_lib.AP_ParamT'int_3.operator_const_int__.pure' this) = this := rfl

/-- C++ `AP_ParamTBase<int, 3>::get : const int &() const`, `AP_Param.h:917-919`. -/
theorem AP_ParamTBase'int_3.get_eq (this : UInt64) :
    Vehicle_lib.AP_ParamTBase'int_3.get this = pure (Vehicle_lib.AP_ParamTBase'int_3.get.pure' this) := rfl

/-- Case: the address of the object itself (the value or member is its first field). -/
theorem AP_ParamTBase'int_3.get_pure_eq (this : UInt64) : Id.run (Vehicle_lib.AP_ParamTBase'int_3.get.pure' this) = this := rfl

end Corpus.AP_Param
