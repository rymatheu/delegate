import ArduLean.Vehicle

/-!
# Integers as the code uses them (fourth increment)

The translation promotes small unsigned values to `int` (`UInt32.toInt32 (UInt16.toUInt32 x)`, `… (UInt8.toUInt32 x)`)
and compares them with `Int32` literals, compares `UInt32` values after `UInt32.toInt32` (signed), and computes addresses
as `this + k` in `UInt64`. These lemmas give each such form its arithmetic meaning. No ArduPilot function appears here.
-/

namespace Corpus.Int

/-- A promoted `uint16_t` is its value. -/
theorem toInt_u16 (x : UInt16) : x.toUInt32.toInt32.toInt = x.toNat := by
  have h := x.toNat_lt
  rw [Int32.toInt, UInt32.toBitVec_toInt32, UInt16.toBitVec_toUInt32, BitVec.toInt_eq_toNat_cond]
  simp
  omega

/-- A promoted `uint8_t` is its value. -/
theorem toInt_u8 (x : UInt8) : x.toUInt32.toInt32.toInt = x.toNat := by
  have h := x.toNat_lt
  rw [Int32.toInt, UInt32.toBitVec_toInt32, UInt8.toBitVec_toUInt32, BitVec.toInt_eq_toNat_cond]
  simp
  omega

/-- A `uint32_t` read as `int`: itself below `2^31`, else wrapped. -/
theorem toInt_u32 (x : UInt32) :
    x.toInt32.toInt = if x.toNat < 2 ^ 31 then (x.toNat : Int) else (x.toNat : Int) - 2 ^ 32 := by
  rw [Int32.toInt, UInt32.toBitVec_toInt32, BitVec.toInt_eq_toNat_cond]
  simp only [UInt32.toNat_toBitVec]
  split_ifs <;> first | rfl | omega

/-- An `Int32` literal below `2^31` is its value. -/
theorem toInt_lit (k : Nat) (hk : k < 2 ^ 31) : (OfNat.ofNat k : Int32).toInt = k := by
  rw [Int32.toInt_ofNat]; simp [Int32.size]; rw [Int.bmod_eq_of_le] <;> omega

theorem beq_u16 (x : UInt16) (k : Nat) (hk : k < 2 ^ 31) :
    (x.toUInt32.toInt32 == (OfNat.ofNat k : Int32)) = true ↔ x.toNat = k := by
  rw [beq_iff_eq, ← Int32.toInt_inj, toInt_u16, toInt_lit k hk]; omega

theorem beq_u8 (x : UInt8) (k : Nat) (hk : k < 2 ^ 31) :
    (x.toUInt32.toInt32 == (OfNat.ofNat k : Int32)) = true ↔ x.toNat = k := by
  rw [beq_iff_eq, ← Int32.toInt_inj, toInt_u8, toInt_lit k hk]; omega

theorem beq_u32 (x : UInt32) (k : Nat) (hk : k < 2 ^ 31) :
    (x.toInt32 == (OfNat.ofNat k : Int32)) = true ↔ x.toNat = k := by
  have := x.toNat_lt
  rw [beq_iff_eq, ← Int32.toInt_inj, toInt_u32, toInt_lit k hk]; split_ifs <;> omega

theorem beq_i32 (x : Int32) (k : Nat) (hk : k < 2 ^ 31) :
    (x == (OfNat.ofNat k : Int32)) = true ↔ x.toInt = k := by
  rw [beq_iff_eq, ← Int32.toInt_inj, toInt_lit k hk]

theorem lt_u8 (x : UInt8) (k : Nat) (hk : k < 2 ^ 31) :
    x.toUInt32.toInt32 < (OfNat.ofNat k : Int32) ↔ x.toNat < k := by
  rw [Int32.lt_iff_toInt_lt, toInt_u8, toInt_lit k hk]; omega

theorem ge_u16 (x : UInt16) (k : Nat) (hk : k < 2 ^ 31) :
    (OfNat.ofNat k : Int32).toInt ≤ x.toUInt32.toInt32.toInt ↔ k ≤ x.toNat := by
  rw [toInt_u16, toInt_lit k hk]; omega

theorem lt_u32 (x : UInt32) (k : Nat) (hk : k < 2 ^ 31) :
    x.toInt32 < (OfNat.ofNat k : Int32) ↔ x.toNat < k ∨ 2 ^ 31 ≤ x.toNat := by
  have := x.toNat_lt
  rw [Int32.lt_iff_toInt_lt, toInt_u32, toInt_lit k hk]; split_ifs <;> omega

/-- An address `a + k` that does not wrap. -/
theorem toNat_add_of_lt {a b : UInt64} (h : a.toNat + b.toNat < 2 ^ 64) : (a + b).toNat = a.toNat + b.toNat := by
  rw [UInt64.toNat_add]; exact Nat.mod_eq_of_lt h

/-- An address `a + k`, wrapping. -/
theorem toNat_add (a b : UInt64) : (a + b).toNat = (a.toNat + b.toNat) % 2 ^ 64 := UInt64.toNat_add a b

end Corpus.Int

namespace Corpus.Int

/-! Equality forms for `simp` (the code's `==` on `Int32` becomes `=`). -/

theorem eq_u16 (x : UInt16) (k : Nat) (hk : k < 2 ^ 31) :
    x.toUInt32.toInt32 = (no_index (OfNat.ofNat k : Int32)) ↔ x.toNat = k := by
  rw [← beq_iff_eq]; exact beq_u16 x k hk

theorem eq_u8 (x : UInt8) (k : Nat) (hk : k < 2 ^ 31) :
    x.toUInt32.toInt32 = (no_index (OfNat.ofNat k : Int32)) ↔ x.toNat = k := by
  rw [← beq_iff_eq]; exact beq_u8 x k hk

theorem eq_u32 (x : UInt32) (k : Nat) (hk : k < 2 ^ 31) :
    x.toInt32 = (no_index (OfNat.ofNat k : Int32)) ↔ x.toNat = k := by
  rw [← beq_iff_eq]; exact beq_u32 x k hk

theorem eq_i32 (x : Int32) (k : Nat) (hk : k < 2 ^ 31) :
    x = (no_index (OfNat.ofNat k : Int32)) ↔ x.toInt = k := by
  rw [← beq_iff_eq]; exact beq_i32 x k hk

end Corpus.Int

/-- A `switch`/`||`-chain on a promoted integer (`uint8_t`, `uint16_t`, `int32_t`), as a statement about the integer's
value: unfold the case split, give each comparison its arithmetic meaning, close by `omega`. -/
macro "table_tac" : tactic => `(tactic| (
  simp only [Id.run, List.mem_cons, List.not_mem_nil, or_false]
  split <;> rename_i h <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, ← Int32.toInt_inj,
      Corpus.Int.toInt_u16, Corpus.Int.toInt_u8, Int32.toInt_ofNat] at h <;>
    simp [Int32.size] at h <;>
    first
      | exact iff_of_true rfl (by omega)
      | exact iff_of_false Bool.false_ne_true (by omega)))

/-- `table_tac` for a `uint32_t` compared as `int` (the comparison wraps at `2^31`). -/
macro "table_tac32" : tactic => `(tactic| (
  simp only [Id.run, List.mem_cons, List.not_mem_nil, or_false]
  have hlt := UInt32.toNat_lt (by assumption)
  split <;> rename_i h <;>
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, ← Int32.toInt_inj,
      Corpus.Int.toInt_u32, Int32.toInt_ofNat] at h <;>
    simp [Int32.size] at h <;>
    split_ifs at h <;>
    first
      | exact iff_of_true rfl (by omega)
      | exact iff_of_false Bool.false_ne_true (by omega)))
