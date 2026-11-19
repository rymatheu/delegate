import ArduLean.Vehicle
import Corpus.Machine.Int

/-!
# AP_Common: `Location.cpp`, `AP_Common.cpp`, `Bitmask.h` (and `AP_CANManager.h`)

Integer leaves with their arithmetic meaning: longitude differences and wrapping, latitude reflection (each with the
inputs for which the `int32_t` results do not overflow), bit-index validity, bounds.
-/

open FloatLib.Floats (Binary32 Binary64)

set_option linter.dupNamespace false

namespace Corpus.AP_Common

/-! ## Longitude and latitude (`Location.cpp`)

Longitudes and latitudes are `int32_t` in units of `1e-7` degrees: `1800000000` is 180°. -/

theorem Location.diff_longitude_eq (lon1 lon2 : Int32) :
    Vehicle_lib.Location.diff_longitude lon1 lon2 = pure (Vehicle_lib.Location.diff_longitude.pure' lon1 lon2) := rfl

/-- Case: with the same sign bit the difference is taken in `int32_t` (`Location.cpp:650-663`). -/
theorem Location.diff_longitude_of_same_sign {lon1 lon2 : Int32}
    (h : ((Int32.toUInt32 lon1 &&& (2147483648 : UInt32)) == (Int32.toUInt32 lon2 &&& (2147483648 : UInt32))) = true) :
    Id.run (Vehicle_lib.Location.diff_longitude.pure' lon1 lon2) = lon1 - lon2 := by
  unfold Vehicle_lib.Location.diff_longitude.pure'
  simp only [Id.run, h, ite_true]; rfl

/-- Meaning: with different sign bits, the difference taken in `int64_t` and wrapped once by `3600000000`
(360°) into `[-1800000000, 1800000000]`. -/
theorem Location.diff_longitude_toInt_of_diff_sign {lon1 lon2 : Int32}
    (h : ¬ ((Int32.toUInt32 lon1 &&& (2147483648 : UInt32)) == (Int32.toUInt32 lon2 &&& (2147483648 : UInt32))) = true) :
    (Id.run (Vehicle_lib.Location.diff_longitude.pure' lon1 lon2)).toInt =
      if lon1.toInt - lon2.toInt > 1800000000 then lon1.toInt - lon2.toInt - 3600000000
      else if lon1.toInt - lon2.toInt < -1800000000 then lon1.toInt - lon2.toInt + 3600000000
      else lon1.toInt - lon2.toInt := by
  have a1 := lon1.le_toInt; have a2 := lon1.toInt_lt; have b1 := lon2.le_toInt; have b2 := lon2.toInt_lt
  unfold Vehicle_lib.Location.diff_longitude.pure'
  simp only [Id.run, h, ite_false, gt_iff_lt, decide_eq_true_eq, Int64.lt_iff_toInt_lt]
  split_ifs <;> simp_all [pure, Int64.toInt_ofNat, Int64.toInt_sub, Int64.toInt_add, Int64.toInt_toInt32, Int64.size, Int32.toInt_sub, Int32.toInt_add, Int32.toInt_neg, Int32.toInt_ofNat, Int32.size, Int.bmod_def] <;> split_ifs <;> omega

/-- Range: with different sign bits, the result is in `[-1800000000, 1800000000]` (±180°). -/
theorem Location.diff_longitude_mem_of_diff_sign {lon1 lon2 : Int32}
    (h : ¬ ((Int32.toUInt32 lon1 &&& (2147483648 : UInt32)) == (Int32.toUInt32 lon2 &&& (2147483648 : UInt32))) = true) :
    -1800000000 ≤ (Id.run (Vehicle_lib.Location.diff_longitude.pure' lon1 lon2)).toInt ∧
      (Id.run (Vehicle_lib.Location.diff_longitude.pure' lon1 lon2)).toInt ≤ 1800000000 := by
  have a1 := lon1.le_toInt; have a2 := lon1.toInt_lt; have b1 := lon2.le_toInt; have b2 := lon2.toInt_lt
  rw [Location.diff_longitude_toInt_of_diff_sign h]
  split_ifs <;> omega

theorem Location.limit_lattitude_eq (lat : Int32) :
    Vehicle_lib.Location.limit_lattitude lat = pure (Vehicle_lib.Location.limit_lattitude.pure' lat) := rfl

/-- Meaning: a latitude beyond ±90° is reflected about the pole (`Location.cpp:668-676`). -/
theorem Location.limit_lattitude_toInt (lat : Int32) :
    (Id.run (Vehicle_lib.Location.limit_lattitude.pure' lat)).toInt =
      if lat.toInt > 900000000 then 1800000000 - lat.toInt
      else if lat.toInt < -900000000 then -(1800000000 + lat.toInt) else lat.toInt := by
  have h1 := lat.le_toInt; have h2 := lat.toInt_lt
  unfold Vehicle_lib.Location.limit_lattitude.pure'
  simp only [Id.run, gt_iff_lt, decide_eq_true_eq, Int64.lt_iff_toInt_lt, Int32.toInt_toInt64, Int64.toInt_neg]
  split_ifs <;> simp_all [pure, Int64.toInt_ofNat, Int64.toInt_sub, Int64.toInt_add, Int64.toInt_toInt32, Int64.size, Int32.toInt_sub, Int32.toInt_add, Int32.toInt_neg, Int32.toInt_ofNat, Int32.size, Int.bmod_def] <;> split_ifs <;> omega

/-- Range: a latitude within ±180° comes back within ±90°. -/
theorem Location.limit_lattitude_mem {lat : Int32} (h1 : -1800000000 ≤ lat.toInt) (h2 : lat.toInt ≤ 1800000000) :
    -900000000 ≤ (Id.run (Vehicle_lib.Location.limit_lattitude.pure' lat)).toInt ∧
      (Id.run (Vehicle_lib.Location.limit_lattitude.pure' lat)).toInt ≤ 900000000 := by
  rw [Location.limit_lattitude_toInt]; split_ifs <;> omega

/-- Case (identity): a latitude within ±90° is unchanged. -/
theorem Location.limit_lattitude_of_mem {lat : Int32} (h1 : -900000000 ≤ lat.toInt) (h2 : lat.toInt ≤ 900000000) :
    Id.run (Vehicle_lib.Location.limit_lattitude.pure' lat) = lat := by
  apply Int32.toInt_inj.1
  rw [Location.limit_lattitude_toInt]; split_ifs <;> omega

theorem Location.wrap_longitude_eq (lon : Int64) :
    Vehicle_lib.Location.wrap_longitude lon = pure (Vehicle_lib.Location.wrap_longitude.pure' lon) := rfl

/-- Meaning: a longitude within ±540° is wrapped once by 360° into ±180° (`Location.cpp:637-645`). -/
theorem Location.wrap_longitude_toInt {lon : Int64} (h1 : -5400000000 ≤ lon.toInt) (h2 : lon.toInt ≤ 5400000000) :
    (Id.run (Vehicle_lib.Location.wrap_longitude.pure' lon)).toInt =
      if lon.toInt > 1800000000 then lon.toInt - 3600000000
      else if lon.toInt < -1800000000 then lon.toInt + 3600000000 else lon.toInt := by
  unfold Vehicle_lib.Location.wrap_longitude.pure'
  simp only [Id.run, gt_iff_lt, decide_eq_true_eq, Int64.lt_iff_toInt_lt]
  split_ifs <;> simp_all [pure, Int64.toInt_ofNat, Int64.toInt_sub, Int64.toInt_add, Int64.toInt_toInt32, Int64.size, Int32.toInt_sub, Int32.toInt_add, Int32.toInt_neg, Int32.toInt_ofNat, Int32.size, Int.bmod_def] <;> split_ifs <;> omega

/-- Range: within ±540° in, within ±180° out. -/
theorem Location.wrap_longitude_mem {lon : Int64} (h1 : -5400000000 ≤ lon.toInt) (h2 : lon.toInt ≤ 5400000000) :
    -1800000000 ≤ (Id.run (Vehicle_lib.Location.wrap_longitude.pure' lon)).toInt ∧
      (Id.run (Vehicle_lib.Location.wrap_longitude.pure' lon)).toInt ≤ 1800000000 := by
  rw [Location.wrap_longitude_toInt h1 h2]; split_ifs <;> omega

/-! ## `Bitmask<N>` (`Bitmask.h`) and `is_bounded_int32` (`AP_Common.cpp`) -/

theorem Bitmask'102.validate_eq (this : UInt64) (bit : UInt16) :
    Vehicle_lib.Bitmask'102.validate this bit = pure (Vehicle_lib.Bitmask'102.validate.pure' this bit) := rfl

/-- Case: a bit index is valid exactly below `102`. -/
theorem Bitmask'102.validate_iff (this : UInt64) (bit : UInt16) :
    Id.run (Vehicle_lib.Bitmask'102.validate.pure' this bit) = true ↔ bit.toNat < 102 := by
  have e := Corpus.Int.toInt_u16 bit
  have k : (UInt32.toInt32 (UInt16.toUInt32 (102 : UInt16))).toInt = 102 := Corpus.Int.toInt_u16 _
  unfold Vehicle_lib.Bitmask'102.validate.pure'
  simp only [Id.run, ge_iff_le, decide_eq_true_eq, Int32.le_iff_toInt_le, e, k]
  split_ifs <;> simp [pure] <;> omega

theorem Bitmask'190.validate_eq (this : UInt64) (bit : UInt16) :
    Vehicle_lib.Bitmask'190.validate this bit = pure (Vehicle_lib.Bitmask'190.validate.pure' this bit) := rfl

/-- Case: a bit index is valid exactly below `190`. -/
theorem Bitmask'190.validate_iff (this : UInt64) (bit : UInt16) :
    Id.run (Vehicle_lib.Bitmask'190.validate.pure' this bit) = true ↔ bit.toNat < 190 := by
  have e := Corpus.Int.toInt_u16 bit
  have k : (UInt32.toInt32 (UInt16.toUInt32 (190 : UInt16))).toInt = 190 := Corpus.Int.toInt_u16 _
  unfold Vehicle_lib.Bitmask'190.validate.pure'
  simp only [Id.run, ge_iff_le, decide_eq_true_eq, Int32.le_iff_toInt_le, e, k]
  split_ifs <;> simp [pure] <;> omega

theorem Bitmask'317.validate_eq (this : UInt64) (bit : UInt16) :
    Vehicle_lib.Bitmask'317.validate this bit = pure (Vehicle_lib.Bitmask'317.validate.pure' this bit) := rfl

/-- Case: a bit index is valid exactly below `317`. -/
theorem Bitmask'317.validate_iff (this : UInt64) (bit : UInt16) :
    Id.run (Vehicle_lib.Bitmask'317.validate.pure' this bit) = true ↔ bit.toNat < 317 := by
  have e := Corpus.Int.toInt_u16 bit
  have k : (UInt32.toInt32 (UInt16.toUInt32 (317 : UInt16))).toInt = 317 := Corpus.Int.toInt_u16 _
  unfold Vehicle_lib.Bitmask'317.validate.pure'
  simp only [Id.run, ge_iff_le, decide_eq_true_eq, Int32.le_iff_toInt_le, e, k]
  split_ifs <;> simp [pure] <;> omega

theorem is_bounded_int32_eq (v lo hi : Int32) :
    Vehicle_lib.is_bounded_int32 v lo hi = pure (Vehicle_lib.is_bounded_int32.pure' v lo hi) := rfl

/-- Case: `lower ≤ upper` and `value` between them (`AP_Common.cpp:32-41`). -/
theorem is_bounded_int32_iff (v lo hi : Int32) :
    Id.run (Vehicle_lib.is_bounded_int32.pure' v lo hi) = true ↔ lo ≤ hi ∧ lo ≤ v ∧ v ≤ hi := by
  unfold Vehicle_lib.is_bounded_int32.pure'
  simp only [Id.run, ge_iff_le, Bool.and_eq_true, decide_eq_true_eq]
  split_ifs with h <;> simp_all [pure, and_assoc]

/-! ## Constant answers (`Bitmask.h`, `AP_CANManager.h`) -/

/-- C++ `Bitmask<317>::size : uint16_t () const`, `stdint.h:155-157`. -/
theorem Bitmask'317.size_eq (this : UInt64) :
    Vehicle_lib.Bitmask'317.size this = pure (Vehicle_lib.Bitmask'317.size.pure' this) := rfl

/-- Protocol: the constant answer. -/
theorem Bitmask'317.size_val (this : UInt64) : Id.run (Vehicle_lib.Bitmask'317.size.pure' this) = 317 := rfl

/-- C++ `AP_CANManager::get_num_drivers : uint8_t () const`, `AP_Common.h:67-70`. -/
theorem AP_CANManager.get_num_drivers_eq (this : UInt64) :
    Vehicle_lib.AP_CANManager.get_num_drivers this = pure (Vehicle_lib.AP_CANManager.get_num_drivers.pure' this) := rfl

/-- Protocol: the constant answer. -/
theorem AP_CANManager.get_num_drivers_val (this : UInt64) : Id.run (Vehicle_lib.AP_CANManager.get_num_drivers.pure' this) = 2 := rfl

end Corpus.AP_Common
