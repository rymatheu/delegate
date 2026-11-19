import ArduLean.Runtime.Memory
import Mathlib.Tactic.IntervalCases
import Corpus.Machine.Loop

/-!
# The byte memory `PMem` as the code uses it

Load-after-store laws for the raw (non-bridged) part of `PMem.Mem.m`, the stack frame (`enter`/`leave`) and `memcpy`,
stated through `StateT.run` (`PMem.M = StateM PMem.Mem`). Every law assumes the addresses lie outside the bridged
range (`PMem.inBridgeN … = false`: there a load or store goes to the estimator World's fields instead) and inside the
memory. No ArduPilot function appears here.
-/

open FloatLib.Floats (Binary32 Binary64)

namespace Corpus.Mem

/-- The 32-bit little-endian word at byte index `i` of `m`, as `PMem.ldU32Raw` assembles it. -/
def w32 (m : ByteArray) (i : Nat) : UInt32 :=
  (m.get! i).toUInt32 ||| ((m.get! (i + 1)).toUInt32 <<< 8) ||| ((m.get! (i + 2)).toUInt32 <<< 16) |||
    ((m.get! (i + 3)).toUInt32 <<< 24)

theorem get!_eq (b : ByteArray) (i : Nat) : b.get! i = b.data[i]! := by
  cases b; rfl

theorem get!_set! (b : ByteArray) (i j : Nat) (v : UInt8) (h : i < b.size) :
    (b.set! i v).get! j = if i = j then v else b.get! j := by
  cases b with
  | mk bs =>
    show (bs.set! i v)[j]! = if i = j then v else bs[j]!
    have h' : i < bs.size := h
    split
    · next hij =>
      subst hij
      simp only [Array.set!_eq_setIfInBounds, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
        Array.getElem?_setIfInBounds_self_of_lt h', Option.getD_some]
    · next hij =>
      simp only [Array.set!_eq_setIfInBounds, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
        Array.getElem?_setIfInBounds_ne hij]

theorem get!_set!_ne (b : ByteArray) (i j : Nat) (v : UInt8) (h : i ≠ j) :
    (b.set! i v).get! j = b.get! j := by
  cases b with
  | mk bs =>
    show (bs.set! i v)[j]! = bs[j]!
    simp only [Array.set!_eq_setIfInBounds, Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?,
      Array.getElem?_setIfInBounds_ne h]

/-- The four bytes of a word reassemble to the word. -/
theorem bytes32 (v : UInt32) :
    (v.toUInt8.toUInt32 ||| ((v >>> 8).toUInt8.toUInt32 <<< 8) ||| ((v >>> 16).toUInt8.toUInt32 <<< 16) |||
      ((v >>> 24).toUInt8.toUInt32 <<< 24)) = v := by
  apply UInt32.toBitVec_inj.1
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [UInt32.toBitVec_or, UInt32.toBitVec_shiftLeft, UInt32.toBitVec_shiftRight, UInt8.toBitVec_toUInt32,
    UInt32.toBitVec_toUInt8, BitVec.getLsbD_or]
  interval_cases i <;> simp

/-- The bytes `stU32Raw` writes. -/
def set4 (m : ByteArray) (i : Nat) (v : UInt32) : ByteArray :=
  (((m.set! i v.toUInt8).set! (i + 1) (v >>> 8).toUInt8).set! (i + 2) (v >>> 16).toUInt8).set! (i + 3)
    (v >>> 24).toUInt8

theorem size_set4 (m : ByteArray) (i : Nat) (v : UInt32) : (set4 m i v).size = m.size := by
  simp [set4]

theorem get!_set4 (m : ByteArray) (i j : Nat) (v : UInt32) (h : i + 4 ≤ m.size) :
    (set4 m i v).get! j =
      if j = i then v.toUInt8 else if j = i + 1 then (v >>> 8).toUInt8 else if j = i + 2 then (v >>> 16).toUInt8
      else if j = i + 3 then (v >>> 24).toUInt8 else m.get! j := by
  unfold set4
  rw [get!_set! _ _ _ _ (by simp; omega), get!_set! _ _ _ _ (by simp; omega), get!_set! _ _ _ _ (by simp; omega),
    get!_set! _ _ _ _ (by omega)]
  by_cases h0 : j = i
  · subst h0; simp
  by_cases h1 : j = i + 1
  · subst h1; simp
  by_cases h2 : j = i + 2
  · subst h2; simp
  by_cases h3 : j = i + 3
  · subst h3; simp
  simp [h0, h1, h2, h3, Ne.symm h0, Ne.symm h1, Ne.symm h2, Ne.symm h3]

theorem w32_set4_self (m : ByteArray) (i : Nat) (v : UInt32) (h : i + 4 ≤ m.size) : w32 (set4 m i v) i = v := by
  unfold w32
  rw [get!_set4 _ _ _ _ h, get!_set4 _ _ _ _ h, get!_set4 _ _ _ _ h, get!_set4 _ _ _ _ h]
  simp only [ite_true, show i + 1 ≠ i by omega, show i + 2 ≠ i by omega, show i + 2 ≠ i + 1 by omega,
    show i + 3 ≠ i by omega, show i + 3 ≠ i + 1 by omega, show i + 3 ≠ i + 2 by omega, ite_false]
  exact bytes32 v

theorem get!_set4_of_lt (m : ByteArray) (i j : Nat) (v : UInt32) (h : j < i ∨ i + 4 ≤ j) :
    (set4 m i v).get! j = m.get! j := by
  unfold set4
  rw [get!_set!_ne _ _ _ _ (by omega), get!_set!_ne _ _ _ _ (by omega), get!_set!_ne _ _ _ _ (by omega),
    get!_set!_ne _ _ _ _ (by omega)]

theorem w32_set4_of_disjoint (m : ByteArray) (i j : Nat) (v : UInt32) (h : j + 4 ≤ i ∨ i + 4 ≤ j) :
    w32 (set4 m i v) j = w32 m j := by
  unfold w32
  rw [get!_set4_of_lt _ _ _ _ (by omega), get!_set4_of_lt _ _ _ _ (by omega), get!_set4_of_lt _ _ _ _ (by omega),
    get!_set4_of_lt _ _ _ _ (by omega)]

/-! ## Block copies (`copySlice`, the fast paths of `memset`, `memcpy`) -/

theorem get!_copySlice (src : ByteArray) (so : Nat) (dest : ByteArray) (d k : Nat) (h1 : d ≤ dest.size)
    (h2 : so + k ≤ src.size) (j : Nat) :
    (src.copySlice so dest d k).get! j =
      if j < d then dest.get! j else if j < d + k then src.get! (so + (j - d)) else dest.get! j := by
  cases src with
  | mk sa =>
  cases dest with
  | mk da =>
  have h1' : d ≤ da.size := h1
  have h2' : so + k ≤ sa.size := h2
  show (da.extract 0 d ++ sa.extract so (so + k) ++ da.extract (d + min k (sa.size - so)) da.size)[j]! =
    if j < d then da[j]! else if j < d + k then sa[so + (j - d)]! else da[j]!
  have hmin : min k (sa.size - so) = k := by omega
  rw [hmin]
  simp only [Array.getElem!_eq_getD, Array.getD_eq_getD_getElem?]
  by_cases ha : j < d
  · rw [Array.getElem?_append_left (by simp; omega), Array.getElem?_append_left (by simp; omega),
      Array.getElem?_extract]
    simp [ha, show j < min d da.size by omega]
  by_cases hb : j < d + k
  · rw [Array.getElem?_append_left (by simp; omega), Array.getElem?_append_right (by simp; omega),
      Array.getElem?_extract]
    simp only [ha, hb, if_false, if_true, Array.size_extract]
    rw [if_pos (by omega)]
    congr 2; simp; omega
  · rw [Array.getElem?_append_right (by simp; omega), Array.getElem?_extract]
    simp only [ha, hb, if_false, Array.size_append, Array.size_extract]
    by_cases hc : j < da.size
    · rw [if_pos (by omega)]; congr 2; simp; omega
    · rw [if_neg (by omega)]
      simp [Array.getElem?_eq_none (show da.size ≤ j by omega)]

/-! ## Loads and stores through the monad -/

/-- An address and width outside the bridged range, inside the memory, without wrap-around. -/
structure Raw (s : PMem.Mem) (a : UInt64) (n : Nat) : Prop where
  bridge : PMem.inBridgeN a n = false
  inside : a.toNat + n ≤ s.m.size
  nowrap : a.toNat + n < 2 ^ 64

theorem ldU32_run {s : PMem.Mem} {a : UInt64} (h : PMem.inBridgeN a 4 = false) :
    (PMem.ldU32 a).run s = (w32 s.m a.toNat, s) := by
  simp [PMem.ldU32, h, PMem.ldU32Raw, w32, StateT.run, get, getThe, MonadStateOf.get, StateT.get, pure,
    StateT.pure, bind, StateT.bind]

theorem ldF32_run {s : PMem.Mem} {a : UInt64} (h : PMem.inBridgeN a 4 = false) :
    (PMem.ldF32 a).run s = (Binary32.ofBits (w32 s.m a.toNat), s) := by
  show (do let w ← PMem.ldU32 a; pure (Binary32.ofBits w) : PMem.M Binary32).run s = _
  rw [StateT.run_bind, ldU32_run h]
  rfl

theorem set!_of_le (b : ByteArray) (i : Nat) (v : UInt8) (h : b.size ≤ i) : b.set! i v = b := by
  cases b with
  | mk bs =>
    show ByteArray.mk (bs.set! i v) = ByteArray.mk bs
    have h' : bs.size ≤ i := h
    congr 1
    simp [Array.set!_eq_setIfInBounds, Array.setIfInBounds, show ¬ i < bs.size by omega]

/-- `wrRaw`'s bounds test is redundant: `set!` out of bounds changes nothing. -/
theorem wrRaw_run (s : PMem.Mem) (a : UInt64) (v : UInt8) :
    (PMem.wrRaw a v).run s = ((), { s with m := s.m.set! a.toNat v }) := by
  simp only [PMem.wrRaw, StateT.run, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, pure]
  split
  · rfl
  · next h => rw [set!_of_le _ _ _ (by omega)]

/-- A raw store of a word: its four bytes, whatever the state (out of bounds they are dropped). -/
theorem stU32_run {s : PMem.Mem} {a : UInt64} {v : UInt32} (hb : PMem.inBridgeN a 4 = false)
    (hnw : a.toNat + 4 < 2 ^ 64) :
    (PMem.stU32 a v).run s = ((), { s with m := set4 s.m a.toNat v }) := by
  have h1 : (a + 1).toNat = a.toNat + 1 := by rw [UInt64.toNat_add]; simp; omega
  have h2 : (a + 2).toNat = a.toNat + 2 := by rw [UInt64.toNat_add]; simp; omega
  have h3 : (a + 3).toNat = a.toNat + 3 := by rw [UInt64.toNat_add]; simp; omega
  simp only [PMem.stU32, hb, Bool.false_eq_true, ite_false, PMem.stU32Raw, StateT.run_bind, wrRaw_run, h1, h2, h3]
  rfl

theorem stF32_run {s : PMem.Mem} {a : UInt64} {x : Binary32} (hb : PMem.inBridgeN a 4 = false)
    (hnw : a.toNat + 4 < 2 ^ 64) :
    (PMem.stF32 a x).run s = ((), { s with m := set4 s.m a.toNat (Binary32.toBits x) }) :=
  stU32_run hb hnw

theorem discard_run {α : Type} (x : PMem.M α) (s : PMem.Mem) :
    (discard x).run s = ((), (x.run s).2) := rfl

theorem run_ite {α : Type} (c : Prop) [Decidable c] (x y : PMem.M α) (s : PMem.Mem) :
    (if c then x else y).run s = if c then x.run s else y.run s := by
  split <;> rfl

theorem leave_run (s : PMem.Mem) (fp : UInt64) : (PMem.leave fp).run s = ((), { s with sp := fp }) := rfl

theorem size_copySlice (src : ByteArray) (so : Nat) (dest : ByteArray) (d k : Nat) (h1 : d + k ≤ dest.size)
    (h2 : so + k ≤ src.size) : (src.copySlice so dest d k).size = dest.size := by
  cases src with
  | mk sa =>
  cases dest with
  | mk da =>
  show (da.extract 0 d ++ sa.extract so (so + k) ++ da.extract (d + min k (sa.size - so)) da.size).size = da.size
  have h1' : d + k ≤ da.size := h1
  have h2' : so + k ≤ sa.size := h2
  simp only [Array.size_append, Array.size_extract]
  omega

theorem get!_extract (a : ByteArray) (b e j : Nat) (h : e ≤ a.size) (hbe : b ≤ e) :
    (a.extract b e).get! j = if j < e - b then a.get! (b + j) else (0 : UInt8) := by
  show (a.copySlice b ByteArray.empty 0 (e - b)).get! j = _
  rw [get!_copySlice _ _ _ _ _ (by simp [ByteArray.size_empty]) (by omega)]
  simp only [Nat.not_lt_zero, ite_false, Nat.zero_add, Nat.sub_zero]
  split_ifs
  · rfl
  · rw [get!_eq]; rfl

theorem zeroBlock_size : PMem.zeroBlock.size = 4096 := by
  simp [PMem.zeroBlock, ByteArray.size]

/-- `enter 4`: a 16-byte frame at the stack pointer, zeroed; the stack pointer moves past it. -/
theorem enter4_run {s : PMem.Mem} (h : Raw s s.sp 16) :
    (PMem.enter 4).run s =
      (s.sp, { s with sp := s.sp + 16, m := PMem.zeroBlock.copySlice 0 s.m s.sp.toNat 16 }) := by
  have hb : PMem.inBridgeN s.sp 16 = false := h.bridge
  have hi := h.inside
  simp only [PMem.enter, PMem.memset, PMem.memsetRaw, StateT.run, bind, StateT.bind, get, getThe,
    MonadStateOf.get, StateT.get, set, StateT.set, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, pure,
    StateT.pure, discard, Functor.mapConst, StateT.map, Function.comp]
  have hz : (Int32.toUInt32 0).toUInt8 = 0 := by decide
  simp [hb, zeroBlock_size, hi, hz, StateT.modifyGet, StateT.bind, StateT.pure]
  rfl

/-- `memcpy d src 4` of two raw, disjoint words. -/
theorem memcpy4_run {s : PMem.Mem} {d src : UInt64} (hd : Raw s d 4) (hs : Raw s src 4)
    (hdisj : d.toNat + 4 ≤ src.toNat ∨ src.toNat + 4 ≤ d.toNat) :
    (PMem.memcpy d src 4).run s =
      (d, { s with m := (s.m.extract src.toNat (src.toNat + 4)).copySlice 0 s.m d.toNat 4 }) := by
  have hb1 : PMem.inBridgeN d 4 = false := hd.bridge
  have hb2 : PMem.inBridgeN src 4 = false := hs.bridge
  have h1 := hd.inside
  have h2 := hs.inside
  have hb1' : PMem.inBridgeN d (4 : UInt64).toNat = false := hb1
  have hb2' : PMem.inBridgeN src (4 : UInt64).toNat = false := hb2
  have hk : (4 : UInt64).toNat = 4 := rfl
  unfold PMem.memcpy
  simp only [hb1', hb2', Bool.or_false, Bool.false_eq_true, ite_false]
  unfold PMem.memcpyRaw
  simp only [StateT.run, bind, StateT.bind, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, pure,
    StateT.pure, hk]
  simp only [show 0 < 4 by omega, h1, h2, decide_true, Bool.true_and, hdisj, Bool.or_eq_true, decide_eq_true_eq,
    ite_true]
  rfl

/-- The frame of `enter 4` leaves every byte outside `[sp, sp + 16)` unchanged. -/
theorem get!_enter4 (m : ByteArray) (sp j : Nat) (h : sp ≤ m.size) (hj : j < sp ∨ sp + 16 ≤ j) :
    (PMem.zeroBlock.copySlice 0 m sp 16).get! j = m.get! j := by
  rw [get!_copySlice _ _ _ _ _ h (by rw [zeroBlock_size]; omega)]
  split_ifs <;> first | omega | rfl

theorem w32_enter4 (m : ByteArray) (sp j : Nat) (h : sp ≤ m.size) (hj : j + 4 ≤ sp ∨ sp + 16 ≤ j) :
    w32 (PMem.zeroBlock.copySlice 0 m sp 16) j = w32 m j := by
  unfold w32
  rw [get!_enter4 _ _ _ h (by omega), get!_enter4 _ _ _ h (by omega), get!_enter4 _ _ _ h (by omega),
    get!_enter4 _ _ _ h (by omega)]

/-- After `memcpy d src 4`, the bytes outside `[d, d + 4)` are unchanged. -/
theorem get!_memcpy4 (m : ByteArray) (d so j : Nat) (hd : d + 4 ≤ m.size) (hs : so + 4 ≤ m.size)
    (hj : j < d ∨ d + 4 ≤ j) :
    ((m.extract so (so + 4)).copySlice 0 m d 4).get! j = m.get! j := by
  rw [get!_copySlice _ _ _ _ _ (by omega) (by simp [ByteArray.size_extract]; omega)]
  split_ifs <;> first | omega | rfl

theorem w32_memcpy4_frame (m : ByteArray) (d so j : Nat) (hd : d + 4 ≤ m.size) (hs : so + 4 ≤ m.size)
    (hj : j + 4 ≤ d ∨ d + 4 ≤ j) :
    w32 ((m.extract so (so + 4)).copySlice 0 m d 4) j = w32 m j := by
  unfold w32
  rw [get!_memcpy4 _ _ _ _ hd hs (by omega), get!_memcpy4 _ _ _ _ hd hs (by omega),
    get!_memcpy4 _ _ _ _ hd hs (by omega), get!_memcpy4 _ _ _ _ hd hs (by omega)]

/-- After `memcpy d src 4`, the word at `d` is the word that was at `src`. -/
theorem w32_memcpy4_dst (m : ByteArray) (d so : Nat) (hd : d + 4 ≤ m.size) (hs : so + 4 ≤ m.size) :
    w32 ((m.extract so (so + 4)).copySlice 0 m d 4) d = w32 m so := by
  unfold w32
  have e : ∀ k, k < 4 → ((m.extract so (so + 4)).copySlice 0 m d 4).get! (d + k) = m.get! (so + k) := by
    intro k hk
    rw [get!_copySlice _ _ _ _ _ (by omega) (by simp [ByteArray.size_extract]; omega),
      get!_extract _ _ _ _ hs (by omega)]
    simp only [show ¬ d + k < d by omega, show d + k < d + 4 by omega, ite_false, ite_true,
      show 0 + (d + k - d) = k by omega, show k < so + 4 - so by omega]
  have e0 : ((m.extract so (so + 4)).copySlice 0 m d 4).get! d = m.get! so := by simpa using e 0 (by omega)
  rw [e0, e 1 (by omega), e 2 (by omega), e 3 (by omega)]

end Corpus.Mem

/-! ## Frames of any size, block copies of any length (second increment) -/

namespace Corpus.Mem

/-- The size of the frame `enter k` makes: `k` rounded up to a multiple of 16. -/
abbrev frameSize (k : Nat) : Nat := (k + 15) / 16 * 16

theorem toNat_toUInt64_of_lt {n : Nat} (h : n < 2 ^ 64) : n.toUInt64.toNat = n := by
  rw [Nat.toUInt64_eq, UInt64.toNat_ofNat_of_lt' h]

/-- `enter k` (`0 < k`, frame at most 4096 bytes, `zeroBlock`'s size): a zeroed frame of `frameSize k` bytes at the
stack pointer; the stack pointer moves past it. -/
theorem enter_run {s : PMem.Mem} {k : Nat} (hk0 : 0 < k) (hk : frameSize k ≤ 4096) (h : Raw s s.sp (frameSize k)) :
    (PMem.enter k).run s =
      (s.sp, { s with sp := s.sp + (frameSize k).toUInt64,
                      m := PMem.zeroBlock.copySlice 0 s.m s.sp.toNat (frameSize k) }) := by
  have hn : (frameSize k).toUInt64.toNat = frameSize k := toNat_toUInt64_of_lt (by omega)
  have hb : PMem.inBridgeN s.sp (frameSize k).toUInt64.toNat = false := by rw [hn]; exact h.bridge
  have hi := h.inside
  have hpos : 0 < frameSize k := by unfold frameSize; omega
  simp only [PMem.enter, PMem.memset, PMem.memsetRaw, StateT.run, bind, StateT.bind, get, getThe,
    MonadStateOf.get, StateT.get, set, StateT.set, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, pure,
    StateT.pure, discard, Functor.mapConst, StateT.map, Function.comp]
  have hz : (Int32.toUInt32 0).toUInt8 = 0 := by decide
  have hk' : (k + 15) / 16 * 16 ≤ 4096 := hk
  have hmod : (k + 15) / 16 * 16 % 18446744073709551616 = (k + 15) / 16 * 16 := Nat.mod_eq_of_lt (by omega)
  have hb' : PMem.inBridgeN s.sp ((k + 15) / 16 * 16) = false := h.bridge
  have hi' : s.sp.toNat + (k + 15) / 16 * 16 ≤ s.m.size := hi
  have hpos' : 0 < (k + 15) / 16 * 16 := hpos
  simp [zeroBlock_size, hi, hz, hn, hpos, hk, hmod, hb', hi', hk', hpos', StateT.modifyGet, StateT.bind,
    StateT.pure]
  rfl

/-- The frame of `enter k` leaves every byte outside `[sp, sp + frameSize k)` unchanged. -/
theorem get!_enter (m : ByteArray) (sp n j : Nat) (h : sp ≤ m.size) (hn : n ≤ 4096) (hj : j < sp ∨ sp + n ≤ j) :
    (PMem.zeroBlock.copySlice 0 m sp n).get! j = m.get! j := by
  rw [get!_copySlice _ _ _ _ _ h (by rw [zeroBlock_size]; omega)]
  split_ifs <;> first | omega | rfl

theorem w32_enter (m : ByteArray) (sp n j : Nat) (h : sp ≤ m.size) (hn : n ≤ 4096) (hj : j + 4 ≤ sp ∨ sp + n ≤ j) :
    w32 (PMem.zeroBlock.copySlice 0 m sp n) j = w32 m j := by
  unfold w32
  rw [get!_enter _ _ _ _ h hn (by omega), get!_enter _ _ _ _ h hn (by omega), get!_enter _ _ _ _ h hn (by omega),
    get!_enter _ _ _ _ h hn (by omega)]

theorem size_enter (m : ByteArray) (sp n : Nat) (h : sp + n ≤ m.size) (hn : n ≤ 4096) :
    (PMem.zeroBlock.copySlice 0 m sp n).size = m.size :=
  size_copySlice _ _ _ _ _ h (by rw [zeroBlock_size]; omega)

/-- `memcpy d src n` (`0 < n`) of two raw, disjoint blocks: one block copy. -/
theorem memcpy_run {s : PMem.Mem} {d src n : UInt64} (hn : 0 < n.toNat) (hd : Raw s d n.toNat)
    (hs : Raw s src n.toNat) (hdisj : d.toNat + n.toNat ≤ src.toNat ∨ src.toNat + n.toNat ≤ d.toNat) :
    (PMem.memcpy d src n).run s =
      (d, { s with m := (s.m.extract src.toNat (src.toNat + n.toNat)).copySlice 0 s.m d.toNat n.toNat }) := by
  have hb1 : PMem.inBridgeN d n.toNat = false := hd.bridge
  have hb2 : PMem.inBridgeN src n.toNat = false := hs.bridge
  have h1 := hd.inside
  have h2 := hs.inside
  unfold PMem.memcpy
  simp only [hb1, hb2, Bool.or_false, Bool.false_eq_true, ite_false]
  unfold PMem.memcpyRaw
  simp only [StateT.run, bind, StateT.bind, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, pure,
    StateT.pure]
  simp only [hn, h1, h2, decide_true, Bool.true_and, hdisj, Bool.or_eq_true, decide_eq_true_eq, ite_true]
  rfl

/-- After `memcpy d src n`, the bytes outside `[d, d + n)` are unchanged. -/
theorem get!_memcpy (m : ByteArray) (d so n j : Nat) (hd : d + n ≤ m.size) (hs : so + n ≤ m.size)
    (hj : j < d ∨ d + n ≤ j) :
    ((m.extract so (so + n)).copySlice 0 m d n).get! j = m.get! j := by
  rw [get!_copySlice _ _ _ _ _ (by omega) (by simp [ByteArray.size_extract]; omega)]
  split_ifs <;> first | omega | rfl

/-- After `memcpy d src n`, the byte at `d + k` (`k < n`) is the byte that was at `src + k`. -/
theorem get!_memcpy_dst (m : ByteArray) (d so n k : Nat) (hd : d + n ≤ m.size) (hs : so + n ≤ m.size) (hk : k < n) :
    ((m.extract so (so + n)).copySlice 0 m d n).get! (d + k) = m.get! (so + k) := by
  rw [get!_copySlice _ _ _ _ _ (by omega) (by simp [ByteArray.size_extract]; omega),
    get!_extract _ _ _ _ hs (by omega)]
  simp only [show ¬ d + k < d by omega, show d + k < d + n by omega, ite_false, ite_true,
    show 0 + (d + k - d) = k by omega, show k < so + n - so by omega]

theorem w32_memcpy_frame (m : ByteArray) (d so n j : Nat) (hd : d + n ≤ m.size) (hs : so + n ≤ m.size)
    (hj : j + 4 ≤ d ∨ d + n ≤ j) :
    w32 ((m.extract so (so + n)).copySlice 0 m d n) j = w32 m j := by
  unfold w32
  rw [get!_memcpy _ _ _ _ _ hd hs (by omega), get!_memcpy _ _ _ _ _ hd hs (by omega),
    get!_memcpy _ _ _ _ _ hd hs (by omega), get!_memcpy _ _ _ _ _ hd hs (by omega)]

/-- After `memcpy d src n`, a word inside the copy is the word at the same offset of the source. -/
theorem w32_memcpy_dst (m : ByteArray) (d so n o : Nat) (hd : d + n ≤ m.size) (hs : so + n ≤ m.size)
    (ho : o + 4 ≤ n) :
    w32 ((m.extract so (so + n)).copySlice 0 m d n) (d + o) = w32 m (so + o) := by
  unfold w32
  rw [show d + o + 1 = d + (o + 1) by omega, show d + o + 2 = d + (o + 2) by omega,
    show d + o + 3 = d + (o + 3) by omega, get!_memcpy_dst _ _ _ _ _ hd hs (by omega),
    get!_memcpy_dst _ _ _ _ _ hd hs (by omega), get!_memcpy_dst _ _ _ _ _ hd hs (by omega),
    get!_memcpy_dst _ _ _ _ _ hd hs (by omega)]
  rfl

theorem size_memcpy (m : ByteArray) (d so n : Nat) (hd : d + n ≤ m.size) (hs : so + n ≤ m.size) :
    ((m.extract so (so + n)).copySlice 0 m d n).size = m.size :=
  size_copySlice _ _ _ _ _ hd (by simp [ByteArray.size_extract]; omega)

/-! ## Regions: the stack and the objects -/

/-- An address range `[a, a + n)` inside a region `[lo, hi)` that lies inside the memory, at or above the end of the
bridged range, below `2^64`. -/
structure InRegion (s : PMem.Mem) (a : UInt64) (lo hi n : Nat) : Prop where
  lo_le : lo ≤ a.toNat
  room : a.toNat + n ≤ hi
  inside : hi ≤ s.m.size
  bridge : PMem.Bridge.hi.toNat ≤ lo
  nowrap : hi < 2 ^ 64

/-- The stack predicate: the stack pointer is in the stack region `[base, top)` with `n` bytes of headroom. -/
abbrev StackOK (s : PMem.Mem) (base top n : Nat) : Prop := InRegion s s.sp base top n

theorem inBridgeN_false_of_ge {a : UInt64} {n : Nat} (h : PMem.Bridge.hi.toNat ≤ a.toNat) :
    PMem.inBridgeN a n = false := by
  unfold PMem.inBridgeN
  have : ¬ a < PMem.Bridge.hi := by rw [UInt64.lt_iff_toNat_lt]; omega
  simp [this]

/-- Every part `[a + o, a + o + w)` of a range in a region is raw (not bridged, inside, no wrap-around). -/
theorem InRegion.raw {s : PMem.Mem} {a : UInt64} {lo hi n : Nat} (h : InRegion s a lo hi n) {o w : Nat}
    (hw : o + w ≤ n) : Raw s (a + o.toUInt64) w := by
  have hn := h.nowrap
  have e : (a + o.toUInt64).toNat = a.toNat + o := by
    rw [UInt64.toNat_add, toNat_toUInt64_of_lt (by have := h.room; omega)]; have := h.room; omega
  refine ⟨inBridgeN_false_of_ge (by rw [e]; have := h.bridge; have := h.lo_le; omega), ?_, ?_⟩
  · rw [e]; have := h.room; have := h.inside; omega
  · rw [e]; have := h.room; omega

theorem InRegion.raw0 {s : PMem.Mem} {a : UInt64} {lo hi n : Nat} (h : InRegion s a lo hi n) {w : Nat}
    (hw : w ≤ n) : Raw s a w := by
  have := h.raw (o := 0) (w := w) (by omega)
  simpa using this

theorem InRegion.toNat_add {s : PMem.Mem} {a : UInt64} {lo hi n : Nat} (h : InRegion s a lo hi n) {o : Nat}
    (ho : o ≤ n) : (a + o.toUInt64).toNat = a.toNat + o := by
  have := h.nowrap; have := h.room
  rw [UInt64.toNat_add, toNat_toUInt64_of_lt (by omega)]; omega

/-- A region predicate depends only on the address and the memory's size. -/
theorem InRegion.congr {s s' : PMem.Mem} {a : UInt64} {lo hi n : Nat} (h : InRegion s a lo hi n)
    (hm : s'.m.size = s.m.size) : InRegion s' a lo hi n :=
  ⟨h.lo_le, h.room, hm ▸ h.inside, h.bridge, h.nowrap⟩

theorem InRegion.mono {s : PMem.Mem} {a : UInt64} {lo hi n n' : Nat} (h : InRegion s a lo hi n) (hn : n' ≤ n) :
    InRegion s a lo hi n' :=
  ⟨h.lo_le, by have := h.room; omega, h.inside, h.bridge, h.nowrap⟩

/-- `enter k` keeps the stack predicate, with `frameSize k` bytes less headroom. -/
theorem StackOK.enter {s : PMem.Mem} {base top n k : Nat} (h : StackOK s base top n) (hk0 : 0 < k)
    (hk : frameSize k ≤ 4096) (hkn : frameSize k ≤ n) :
    StackOK ((PMem.enter k).run s).2 base top (n - frameSize k) := by
  rw [enter_run hk0 hk (h.raw0 hkn)]
  have hs : (s.sp + (frameSize k).toUInt64).toNat = s.sp.toNat + frameSize k := h.toNat_add hkn
  refine ⟨?_, ?_, ?_, h.bridge, h.nowrap⟩
  · show base ≤ (s.sp + (frameSize k).toUInt64).toNat; rw [hs]; have := h.lo_le; omega
  · show (s.sp + (frameSize k).toUInt64).toNat + (n - frameSize k) ≤ top; rw [hs]; have := h.room; omega
  · show top ≤ (PMem.zeroBlock.copySlice 0 s.m s.sp.toNat (frameSize k)).size
    rw [size_enter _ _ _ (by have := h.room; have := h.inside; omega) hk]; exact h.inside

/-- `leave` restores the stack pointer, so the stack predicate of the caller's state holds again. -/
theorem StackOK.leave {s s' : PMem.Mem} {base top n : Nat} (h : StackOK s base top n)
    (hm : s'.m.size = s.m.size) : StackOK ((PMem.leave s.sp).run s').2 base top n := by
  rw [leave_run]; exact ⟨h.lo_le, h.room, hm ▸ h.inside, h.bridge, h.nowrap⟩

/-- Two ranges in disjoint regions (`hi₁ ≤ lo₂`) are disjoint. -/
theorem InRegion.disjoint {s : PMem.Mem} {a b : UInt64} {lo₁ hi₁ lo₂ hi₂ n m : Nat} (ha : InRegion s a lo₁ hi₁ n)
    (hb : InRegion s b lo₂ hi₂ m) (h : hi₁ ≤ lo₂) : a.toNat + n ≤ b.toNat := by
  have := ha.room; have := hb.lo_le; omega

end Corpus.Mem

/-! ## Byte loads and stores -/

namespace Corpus.Mem

theorem inBridge_false_of_ge {a : UInt64} (h : PMem.Bridge.hi.toNat ≤ a.toNat) : PMem.inBridge a = false := by
  unfold PMem.inBridge
  have : ¬ a < PMem.Bridge.hi := by rw [UInt64.lt_iff_toNat_lt]; omega
  simp [this]

theorem ldU8_run {s : PMem.Mem} {a : UInt64} (h : PMem.inBridge a = false) :
    (PMem.ldU8 a).run s = (s.m.get! a.toNat, s) := by
  simp [PMem.ldU8, PMem.rd, h, PMem.rdRaw, StateT.run, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure,
    bind, StateT.bind]

theorem ldB_run {s : PMem.Mem} {a : UInt64} (h : PMem.inBridge a = false) :
    (PMem.ldB a).run s = (s.m.get! a.toNat != 0, s) := by
  show (do let b ← PMem.ldU8 a; pure (b != 0) : PMem.M Bool).run s = _
  rw [StateT.run_bind, ldU8_run h]; rfl

theorem stU8_run {s : PMem.Mem} {a : UInt64} {v : UInt8} (h : PMem.inBridge a = false) :
    (PMem.stU8 a v).run s = ((), { s with m := s.m.set! a.toNat v }) := by
  show (PMem.wr a v).run s = _
  simp only [PMem.wr, h, Bool.false_eq_true, ite_false]
  exact wrRaw_run s a v

theorem stB_run {s : PMem.Mem} {a : UInt64} {v : Bool} (h : PMem.inBridge a = false) :
    (PMem.stB a v).run s = ((), { s with m := s.m.set! a.toNat (if v then 1 else 0) }) :=
  stU8_run h

theorem size_set! (b : ByteArray) (i : Nat) (v : UInt8) : (b.set! i v).size = b.size := by
  cases b; simp [ByteArray.set!, ByteArray.size]

theorem w32_set!_of_disjoint (m : ByteArray) (i j : Nat) (v : UInt8) (h : i < j ∨ j + 4 ≤ i) :
    w32 (m.set! i v) j = w32 m j := by
  unfold w32
  rw [get!_set!_ne _ _ _ _ (by omega), get!_set!_ne _ _ _ _ (by omega), get!_set!_ne _ _ _ _ (by omega),
    get!_set!_ne _ _ _ _ (by omega)]

end Corpus.Mem

/-! ## Bit-fields, signed bytes, double words; loads leave the state unchanged (third increment) -/

namespace Corpus.Mem

/-- Bit `o` of the byte `b`, as `PMem.ldBits` returns it (a `UInt64` that is `0` or `1`). -/
def bitOf (b : UInt8) (o : Nat) : UInt64 := if b.toNat >>> o % 2 = 1 then 1 else 0

/-- The byte `b` with bit `o` set (`c`) or cleared, as `PMem.stBits` writes it. -/
def setBit (b : UInt8) (o : Nat) (c : Bool) : UInt8 :=
  if c then b ||| (1 : UInt8) <<< o.toUInt8 else b &&& ~~~((1 : UInt8) <<< o.toUInt8)

/-- A one-bit field at bit `o < 8` of a raw byte. -/
theorem ldBits_run {s : PMem.Mem} {a : UInt64} {o : Nat} (h : PMem.inBridge a = false) (ho : o < 8) :
    (PMem.ldBits a o 1).run s = (bitOf (s.m.get! a.toNat) o, s) := by
  unfold PMem.ldBits
  simp only [Corpus.Loop.forIn_range_0_1]
  simp [StateT.run, List.forIn_cons, PMem.rd, h, PMem.rdRaw, show o / 8 = 0 by omega, Nat.mod_eq_of_lt ho, bind,
    StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure, bitOf]
  by_cases hc : (s.m.get! a.toNat).toNat >>> o % 2 = 1 <;> simp [hc] <;> rfl

/-- A store into a one-bit field at bit `o < 8` of a raw byte: the byte with that bit replaced by bit 0 of `v`. -/
theorem stBits_run {s : PMem.Mem} {a : UInt64} {o : Nat} {v : UInt64} (h : PMem.inBridge a = false) (ho : o < 8) :
    (PMem.stBits a o 1 v).run s =
      ((), { s with m := s.m.set! a.toNat (setBit (s.m.get! a.toNat) o (v.toNat % 2 = 1)) }) := by
  unfold PMem.stBits
  simp only [Corpus.Loop.forIn_range_0_1]
  simp [StateT.run, List.forIn_cons, PMem.rd, PMem.wr, h, PMem.rdRaw, show o / 8 = 0 by omega,
    Nat.mod_eq_of_lt ho, bind, StateT.bind, get, getThe, MonadStateOf.get, StateT.get, pure, StateT.pure, setBit,
    PMem.wrRaw, modify, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet]
  split
  · rfl
  · next hs => rw [set!_of_le _ _ _ (by omega)]

/-- The bit-field law on bytes: the bit just written reads back. -/
theorem bitOf_setBit_self (b : UInt8) (o : Nat) (ho : o < 8) (c : Bool) :
    bitOf (setBit b o c) o = if c then 1 else 0 := by
  have key : ∀ (b : UInt8) (o : Fin 8) (c : Bool), bitOf (setBit b o.val c) o.val = if c then 1 else 0 := by
    decide +kernel
  exact key b ⟨o, ho⟩ c

/-- The bit-field law on bytes: the other bits of the byte are unchanged. -/
theorem bitOf_setBit_ne (b : UInt8) (o o' : Nat) (ho : o < 8) (ho' : o' < 8) (hne : o ≠ o') (c : Bool) :
    bitOf (setBit b o c) o' = bitOf b o' := by
  have key : ∀ (b : UInt8) (o o' : Fin 8) (c : Bool), o ≠ o' → bitOf (setBit b o.val c) o'.val = bitOf b o'.val := by
    decide +kernel
  exact key b ⟨o, ho⟩ ⟨o', ho'⟩ c (fun e => hne (congrArg Fin.val e))

/-- Store then load, one-bit field: the stored bit reads back. -/
theorem ldBits_stBits_self {s : PMem.Mem} {a : UInt64} {o : Nat} {v : UInt64} (h : PMem.inBridge a = false)
    (ho : o < 8) (hin : a.toNat < s.m.size) :
    ((PMem.ldBits a o 1).run ((PMem.stBits a o 1 v).run s).2).1 = v % 2 := by
  rw [stBits_run h ho, ldBits_run h ho]
  simp only
  rw [get!_set! _ _ _ _ hin, if_pos rfl, bitOf_setBit_self _ _ ho]
  have : v.toNat % 2 = 0 ∨ v.toNat % 2 = 1 := by omega
  rcases this with e | e
  · simp only [e, show (0 : Nat) ≠ 1 by decide, decide_false, ite_false]
    apply UInt64.toNat_inj.1; simp [UInt64.toNat_mod, e]
  · simp only [e, decide_true, ite_true]
    apply UInt64.toNat_inj.1; simp [UInt64.toNat_mod, e]

/-- Store then load, one-bit field: another bit of the same byte is unchanged. -/
theorem ldBits_stBits_ne {s : PMem.Mem} {a : UInt64} {o o' : Nat} {v : UInt64} (h : PMem.inBridge a = false)
    (ho : o < 8) (ho' : o' < 8) (hne : o ≠ o') (hin : a.toNat < s.m.size) :
    ((PMem.ldBits a o' 1).run ((PMem.stBits a o 1 v).run s).2).1 = ((PMem.ldBits a o' 1).run s).1 := by
  rw [stBits_run h ho, ldBits_run h ho', ldBits_run h ho']
  simp only
  rw [get!_set! _ _ _ _ hin, if_pos rfl, bitOf_setBit_ne _ _ _ ho ho' hne]

/-- A one-bit store changes no byte other than its own. -/
theorem stBits_get!_ne {s : PMem.Mem} {a : UInt64} {o : Nat} {v : UInt64} (h : PMem.inBridge a = false)
    (ho : o < 8) {j : Nat} (hj : j ≠ a.toNat) :
    ((PMem.stBits a o 1 v).run s).2.m.get! j = s.m.get! j := by
  rw [stBits_run h ho]; exact get!_set!_ne _ _ _ _ (Ne.symm hj)

/-- A signed byte. -/
theorem ldI8_run {s : PMem.Mem} {a : UInt64} (h : PMem.inBridge a = false) :
    (PMem.ldI8 a).run s = ((s.m.get! a.toNat).toInt8, s) := by
  show (do let b ← PMem.ldU8 a; pure b.toInt8 : PMem.M Int8).run s = _
  rw [StateT.run_bind, ldU8_run h]; rfl

/-- A raw 8-byte word (a pointer): two raw 4-byte words, little-endian. -/
theorem ldU64_run {s : PMem.Mem} {a : UInt64} (h0 : PMem.inBridgeN a 4 = false)
    (h4 : PMem.inBridgeN (a + 4) 4 = false) :
    (PMem.ldU64 a).run s = ((w32 s.m a.toNat).toUInt64 ||| ((w32 s.m (a + 4).toNat).toUInt64 <<< 32), s) := by
  show (do let lo ← PMem.ldU32 a; let hi ← PMem.ldU32 (a + 4); pure (lo.toUInt64 ||| (hi.toUInt64 <<< 32)) :
    PMem.M UInt64).run s = _
  rw [StateT.run_bind, ldU32_run h0]
  show (do let hi ← PMem.ldU32 (a + 4); pure _ : PMem.M UInt64).run s = _
  rw [StateT.run_bind, ldU32_run h4]; rfl

/-! Every load, at any address (bridged or not, inside the memory or not), leaves the state unchanged. -/

/-- A bind in `PMem.M`, through `StateT.run`: the continuation runs from the first part's state. -/
theorem run_bind' {α β : Type} (x : PMem.M α) (f : α → PMem.M β) (s : PMem.Mem) :
    (x >>= f).run s = (f (x.run s).1).run (x.run s).2 := rfl

theorem rd_state (a : UInt64) (s : PMem.Mem) : ((PMem.rd a).run s).2 = s := by
  unfold PMem.rd PMem.rdField PMem.rdRaw
  split
  · split <;> rfl
  · rfl

theorem ldU8_state (a : UInt64) (s : PMem.Mem) : ((PMem.ldU8 a).run s).2 = s := rd_state a s

theorem ldB_state (a : UInt64) (s : PMem.Mem) : ((PMem.ldB a).run s).2 = s := by
  show ((do let b ← PMem.ldU8 a; pure (b != 0) : PMem.M Bool).run s).2 = s
  rw [StateT.run_bind]; exact ldU8_state a s

theorem ldI8_state (a : UInt64) (s : PMem.Mem) : ((PMem.ldI8 a).run s).2 = s := by
  show ((do let b ← PMem.ldU8 a; pure b.toInt8 : PMem.M Int8).run s).2 = s
  rw [StateT.run_bind]; exact ldU8_state a s

theorem ldWord_state (a : UInt64) (n : Nat) (s : PMem.Mem) : ((PMem.ldWord a n).run s).2 = s := by
  have hloop : ∀ (v : UInt64), ((forIn (m := PMem.M) [0:n] v fun k r => do
      let x ← PMem.rd (a + k.toUInt64)
      pure (ForInStep.yield (r ||| x.toUInt64 <<< (8 * k).toUInt64))).run s).2 = s := by
    intro v
    refine Corpus.Loop.forIn_range_state _ 0 n (fun i c s' => ?_) v s
    rw [StateT.run_bind]; exact rd_state _ _
  unfold PMem.ldWord
  split
  · split
    · rfl
    · simp only [StateT.run_bind]; exact hloop 0
  · simp only [StateT.run_bind]; exact hloop 0

theorem ldU32_state (a : UInt64) (s : PMem.Mem) : ((PMem.ldU32 a).run s).2 = s := by
  unfold PMem.ldU32
  split
  · rw [StateT.run_bind]; exact ldWord_state a 4 s
  · rfl

theorem ldF32_state (a : UInt64) (s : PMem.Mem) : ((PMem.ldF32 a).run s).2 = s := by
  show ((do let w ← PMem.ldU32 a; pure (Binary32.ofBits w) : PMem.M Binary32).run s).2 = s
  rw [StateT.run_bind]; exact ldU32_state a s

theorem ldU64_state (a : UInt64) (s : PMem.Mem) : ((PMem.ldU64 a).run s).2 = s := by
  show ((do let lo ← PMem.ldU32 a; let hi ← PMem.ldU32 (a + 4); pure (lo.toUInt64 ||| (hi.toUInt64 <<< 32)) :
    PMem.M UInt64).run s).2 = s
  rw [run_bind', ldU32_state, run_bind', ldU32_state]; rfl

theorem ldBits_state (a : UInt64) (o w : Nat) (s : PMem.Mem) : ((PMem.ldBits a o w).run s).2 = s := by
  unfold PMem.ldBits
  rw [run_bind']
  show ((pure _ : PMem.M UInt64).run _).2 = s
  rw [Corpus.Loop.forIn_range_state _ 0 w ?_ _ s]
  · rfl
  · intro i c s'
    rw [run_bind', rd_state]
    split <;> rfl

end Corpus.Mem
