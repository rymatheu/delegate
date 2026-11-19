import ArduLean.Vehicle
import Corpus.Machine.Float
import Corpus.Machine.Memory
import Corpus.Code.AP_Param.AP_Param
import Corpus.Code.AP_Math.AP_Math
import Corpus.Machine.Hoare
import Corpus.Code.Filter.SlewLimiter

/-!
# AC_PID: `AC_PID.cpp` (tier 1 trial)

C++ `AC_PID::update_i : void (float, bool, float)`, `AC_PID.cpp:340-351`:

    if (!is_zero(_ki) && is_positive(dt)) {
        if (!limit || ((is_positive(_integrator) && is_negative(_error)) || (is_negative(_integrator) && is_positive(_error)))) {
            _integrator += ((float)_error * _ki) * i_scale * dt;
            _integrator = constrain_float(_integrator, -_kimax, _kimax);
        }
    } else {
        _integrator = 0.0f;
    }

Fields of `AC_PID` at `this` (clang's layout): `_ki` at `+4`, `_kimax` at `+16`, `_integrator` at `+132`, `_error` at
`+140`. The translation copies `_ki` into a 16-byte stack frame (`is_zero` takes the `AP_Float` by value).
-/

open FloatLib.Floats (Binary32 Binary64)
open Corpus.Mem (w32 set4 Raw)

namespace Corpus.AC_PID

/-- The memory after `update_i`'s frame (`enter 4`, zeroed) and its copy of `_ki` to the frame. -/
def frameMem (m : ByteArray) (this sp : UInt64) : ByteArray :=
  ((PMem.zeroBlock.copySlice 0 m sp.toNat 16).extract (this + 4).toNat ((this + 4).toNat + 4)).copySlice
    0 (PMem.zeroBlock.copySlice 0 m sp.toNat 16) sp.toNat 4

/-- The memory after the update branch, which stores `x` and then `constrain_float(x', -kimax, kimax)` (`x'` and
`kimax` read back from memory) into `_integrator`. -/
abbrev updMem (m1 : ByteArray) (this : UInt64) (x : Binary32) : ByteArray :=
  set4 (set4 m1 (this + 132).toNat (Binary32.toBits x)) (this + 132).toNat
    (Binary32.toBits (Vehicle_lib.constrain_value_line'float.pure'
      (Binary32.ofBits (w32 (set4 m1 (this + 132).toNat (Binary32.toBits x)) (this + 132).toNat))
      (-(Binary32.ofBits (w32 (set4 m1 (this + 132).toNat (Binary32.toBits x)) (this + 16).toNat)))
      (Binary32.ofBits (w32 (set4 m1 (this + 132).toNat (Binary32.toBits x)) (this + 16).toNat))
      (Int32.toUInt32 346)))

/-- The hypotheses of the trial: the frame and the four fields are raw (not bridged), inside the memory, without
wrap-around, and the frame `[sp, sp + 16)` is disjoint from the object's bytes `[this + 4, this + 144)`. -/
structure Pre (s : PMem.Mem) (this : UInt64) : Prop where
  frame : Raw s s.sp 16
  fp : PMem.inBridgeN s.sp 4 = false
  ki : Raw s (this + 4) 4
  kimax : Raw s (this + 16) 4
  integ : Raw s (this + 132) 4
  err : Raw s (this + 140) 4
  nowrap : this.toNat + 144 < 2 ^ 64
  disj : s.sp.toNat + 16 ≤ this.toNat + 4 ∨ this.toNat + 144 ≤ s.sp.toNat

private theorem Pre.toNat4 {s : PMem.Mem} {this : UInt64} (h : Pre s this) : (this + 4).toNat = this.toNat + 4 := by
  have := h.nowrap; rw [UInt64.toNat_add]; simp; omega
private theorem Pre.toNat16 {s : PMem.Mem} {this : UInt64} (h : Pre s this) : (this + 16).toNat = this.toNat + 16 := by
  have := h.nowrap; rw [UInt64.toNat_add]; simp; omega
private theorem Pre.toNat132 {s : PMem.Mem} {this : UInt64} (h : Pre s this) : (this + 132).toNat = this.toNat + 132 := by
  have := h.nowrap; rw [UInt64.toNat_add]; simp; omega
private theorem Pre.toNat140 {s : PMem.Mem} {this : UInt64} (h : Pre s this) : (this + 140).toNat = this.toNat + 140 := by
  have := h.nowrap; rw [UInt64.toNat_add]; simp; omega

/-- The three shapes of the state `update_i` leaves: the state as it was except for the memory, which is the frame
alone (no update), `_integrator` zeroed, or the update branch's two stores (`updMem`). -/
def Shape (s : PMem.Mem) (this : UInt64) (r : Unit × PMem.Mem) : Prop :=
  ∃ m', r = ((), { s with m := m' }) ∧
    (m' = frameMem s.m this s.sp ∨
      m' = set4 (frameMem s.m this s.sp) (this + 132).toNat (Binary32.toBits (Binary32.ofBits 0x00000000)) ∨
      ∃ x, m' = updMem (frameMem s.m this s.sp) this x)

/-- The same shapes for the body's result, before `leave` restores the stack pointer. -/
def BodyShape (s : PMem.Mem) (this : UInt64) (r : Unit × PMem.Mem) : Prop :=
  ∃ m', r = ((), { s with sp := s.sp + 16, m := m' }) ∧
    (m' = frameMem s.m this s.sp ∨
      m' = set4 (frameMem s.m this s.sp) (this + 132).toNat (Binary32.toBits (Binary32.ofBits 0x00000000)) ∨
      ∃ x, m' = updMem (frameMem s.m this s.sp) this x)

private theorem BodyShape.ite {s : PMem.Mem} {this : UInt64} {c : Prop} [Decidable c] {a b : Unit × PMem.Mem}
    (ha : BodyShape s this a) (hb : BodyShape s this b) : BodyShape s this (if c then a else b) := by
  split <;> assumption

private theorem BodyShape.leave {s : PMem.Mem} {this : UInt64} {r : Unit × PMem.Mem} (hr : BodyShape s this r) :
    Shape s this (r.1, { r.2 with sp := s.sp }) := by
  obtain ⟨m', rfl, hm⟩ := hr
  exact ⟨m', rfl, hm⟩

/-- Effect: `update_i` leaves the state in one of the three shapes. -/
theorem update_i_shape {s : PMem.Mem} {this : UInt64} (h : Pre s this) (dt : Binary32) (limit : Bool)
    (isc : Binary32) : Shape s this ((Vehicle_lib.AC_PID.update_i this dt limit isc).run s) := by
  have hsp0 : s.sp + 0 = s.sp := by simp
  have hsz0 : (PMem.zeroBlock.copySlice 0 s.m s.sp.toNat 16).size = s.m.size :=
    Corpus.Mem.size_copySlice _ _ _ _ _ h.frame.inside (by rw [Corpus.Mem.zeroBlock_size]; omega)
  have hd : Raw { s with sp := s.sp + 16, m := PMem.zeroBlock.copySlice 0 s.m s.sp.toNat 16 } (s.sp + 0) 4 :=
    ⟨by rw [hsp0]; exact h.fp, by rw [hsp0]; simp only [hsz0]; have := h.frame.inside; omega,
     by rw [hsp0]; have := h.frame.nowrap; omega⟩
  have hs : Raw { s with sp := s.sp + 16, m := PMem.zeroBlock.copySlice 0 s.m s.sp.toNat 16 } (this + 4) 4 :=
    ⟨h.ki.bridge, by simp only [hsz0]; exact h.ki.inside, h.ki.nowrap⟩
  have hdisj : (s.sp + 0).toNat + 4 ≤ (this + 4).toNat ∨ (this + 4).toNat + 4 ≤ (s.sp + 0).toNat := by
    rw [hsp0, h.toNat4]; have := h.disj; omega
  unfold Vehicle_lib.AC_PID.update_i
  rw [StateT.run_bind, Corpus.Mem.enter4_run h.frame]
  simp only [Corpus.id_bind, Corpus.id_run_eq]
  rw [StateT.run_bind]
  unfold Vehicle_lib.AC_PID.update_i.body
  simp only [StateT.run_bind, Corpus.Mem.discard_run, Corpus.Mem.memcpy4_run hd hs hdisj]
  simp only [Corpus.id_bind, Corpus.id_run_eq, StateT.run_bind, hsp0,
    Corpus.AP_Math.is_zero_param_run h.fp, Corpus.AP_Math.is_positive_eq, Corpus.AP_Math.is_negative_eq,
    Corpus.Mem.ldF32_run h.integ.bridge, Corpus.Mem.ldF32_run h.err.bridge, Corpus.Mem.ldF32_run h.ki.bridge,
    Corpus.Mem.ldF32_run h.kimax.bridge, Corpus.Mem.stF32_run h.integ.bridge h.integ.nowrap,
    Corpus.AP_Param.operator_const_float_run, Corpus.AP_Param.operator_neg_run h.kimax.bridge,
    Corpus.AP_Math.constrain_float_eq, StateT.run_pure, Corpus.Mem.leave_run, Corpus.Mem.run_ite,
    Corpus.Mem.discard_run, Corpus.id_pure_eq]
  rw [show ((PMem.zeroBlock.copySlice 0 s.m s.sp.toNat 16).extract (this + 4).toNat
      ((this + 4).toNat + 4)).copySlice 0 (PMem.zeroBlock.copySlice 0 s.m s.sp.toNat 16) s.sp.toNat 4 =
      frameMem s.m this s.sp from rfl]
  clear hd hs hdisj hsz0 hsp0
  generalize Vehicle_lib.is_zero.pure' = Z
  generalize Vehicle_lib.is_positive'float.pure' = P
  generalize Vehicle_lib.is_negative'float.pure' = N
  apply BodyShape.leave
  repeat
    first
    | exact ⟨_, by with_reducible rfl, Or.inl (by with_reducible rfl)⟩
    | exact ⟨_, by with_reducible rfl, Or.inr (Or.inl (by with_reducible rfl))⟩
    | exact ⟨_, by with_reducible rfl, Or.inr (Or.inr ⟨_, by with_reducible rfl⟩)⟩
    | apply BodyShape.ite

/-! ## Effect and Invariant -/

private theorem frameMem_size {s : PMem.Mem} {this : UInt64} (h : Pre s this) :
    (frameMem s.m this s.sp).size = s.m.size := by
  have hsz0 : (PMem.zeroBlock.copySlice 0 s.m s.sp.toNat 16).size = s.m.size :=
    Corpus.Mem.size_copySlice _ _ _ _ _ h.frame.inside (by rw [Corpus.Mem.zeroBlock_size]; omega)
  unfold frameMem
  have hk := h.ki.inside
  have hex : ((PMem.zeroBlock.copySlice 0 s.m s.sp.toNat 16).extract (this + 4).toNat
      ((this + 4).toNat + 4)).size = 4 := by
    rw [ByteArray.size_extract, hsz0]; omega
  rw [Corpus.Mem.size_copySlice _ _ _ _ _ (by rw [hsz0]; have := h.frame.inside; omega) (by rw [hex]), hsz0]

/-- The frame and the copy of `_ki` change no byte outside the frame. -/
private theorem frameMem_get! {s : PMem.Mem} {this : UInt64} (h : Pre s this) {j : Nat}
    (hj : j < s.sp.toNat ∨ s.sp.toNat + 16 ≤ j) : (frameMem s.m this s.sp).get! j = s.m.get! j := by
  have hsz0 : (PMem.zeroBlock.copySlice 0 s.m s.sp.toNat 16).size = s.m.size :=
    Corpus.Mem.size_copySlice _ _ _ _ _ h.frame.inside (by rw [Corpus.Mem.zeroBlock_size]; omega)
  unfold frameMem
  have := h.frame.inside
  have := h.ki.inside
  rw [Corpus.Mem.get!_memcpy4 _ _ _ _ (by rw [hsz0]; omega) (by rw [hsz0]; omega) (by omega),
    Corpus.Mem.get!_enter4 _ _ _ (by omega) hj]

/-- Effect: `update_i` changes no byte outside `_integrator` (`[this + 132, this + 136)`) and its stack frame
(`[sp, sp + 16)`), and no part of the state other than the memory. -/
theorem update_i_frame {s : PMem.Mem} {this : UInt64} (h : Pre s this) (dt : Binary32) (limit : Bool)
    (isc : Binary32) {j : Nat} (hj1 : j < (this + 132).toNat ∨ (this + 132).toNat + 4 ≤ j)
    (hj2 : j < s.sp.toNat ∨ s.sp.toNat + 16 ≤ j) :
    ((Vehicle_lib.AC_PID.update_i this dt limit isc).run s).2 =
        { s with m := ((Vehicle_lib.AC_PID.update_i this dt limit isc).run s).2.m } ∧
      ((Vehicle_lib.AC_PID.update_i this dt limit isc).run s).2.m.get! j = s.m.get! j := by
  obtain ⟨m', hr, hm⟩ := update_i_shape h dt limit isc
  rw [hr]
  refine ⟨rfl, ?_⟩
  simp only
  rcases hm with rfl | rfl | ⟨x, rfl⟩
  · exact frameMem_get! h hj2
  · rw [Corpus.Mem.get!_set4_of_lt _ _ _ _ (by omega), frameMem_get! h hj2]
  · rw [Corpus.Mem.get!_set4_of_lt _ _ _ _ (by omega), Corpus.Mem.get!_set4_of_lt _ _ _ _ (by omega),
      frameMem_get! h hj2]

/-- Effect: the word at a field `[a, a + 4)` disjoint from `_integrator` and from the frame is unchanged. -/
theorem update_i_w32 {s : PMem.Mem} {this : UInt64} (h : Pre s this) (dt : Binary32) (limit : Bool)
    (isc : Binary32) {a : Nat} (h1 : a + 4 ≤ (this + 132).toNat ∨ (this + 132).toNat + 4 ≤ a)
    (h2 : a + 4 ≤ s.sp.toNat ∨ s.sp.toNat + 16 ≤ a) :
    w32 ((Vehicle_lib.AC_PID.update_i this dt limit isc).run s).2.m a = w32 s.m a := by
  unfold w32
  rw [(update_i_frame h dt limit isc (j := a) (by omega) (by omega)).2,
    (update_i_frame h dt limit isc (j := a + 1) (by omega) (by omega)).2,
    (update_i_frame h dt limit isc (j := a + 2) (by omega) (by omega)).2,
    (update_i_frame h dt limit isc (j := a + 3) (by omega) (by omega)).2]

/-- Effect: `_kimax` is unchanged. -/
theorem update_i_kimax {s : PMem.Mem} {this : UInt64} (h : Pre s this) (dt : Binary32) (limit : Bool)
    (isc : Binary32) :
    w32 ((Vehicle_lib.AC_PID.update_i this dt limit isc).run s).2.m (this + 16).toNat = w32 s.m (this + 16).toNat :=
  update_i_w32 h dt limit isc (by rw [h.toNat16, h.toNat132]; omega) (by rw [h.toNat16]; have := h.disj; omega)

/-- Case/Effect: the integrator after the call is the integrator before (no update), `0`, or
`constrain_float(x, -kimax, kimax)` for the updated value `x` (the update branch). -/
theorem update_i_integrator {s : PMem.Mem} {this : UInt64} (h : Pre s this) (dt : Binary32) (limit : Bool)
    (isc : Binary32) :
    let I' := Binary32.ofBits (w32 ((Vehicle_lib.AC_PID.update_i this dt limit isc).run s).2.m (this + 132).toNat)
    let M := Binary32.ofBits (w32 s.m (this + 16).toNat)
    I' = Binary32.ofBits (w32 s.m (this + 132).toNat) ∨ I' = Binary32.ofBits 0x00000000 ∨
      ∃ x, I' = Id.run (Vehicle_lib.constrain_value_line'float.pure' x (-M) M (Int32.toUInt32 346)) := by
  intro I' M
  have hsz := frameMem_size h
  have hin := h.integ.inside
  have hfr : ∀ a : Nat, a + 4 ≤ s.sp.toNat ∨ s.sp.toNat + 16 ≤ a → w32 (frameMem s.m this s.sp) a = w32 s.m a := by
    intro a ha
    unfold w32
    rw [frameMem_get! h (by omega), frameMem_get! h (by omega), frameMem_get! h (by omega),
      frameMem_get! h (by omega)]
  have h132 : (this + 132).toNat + 4 ≤ s.sp.toNat ∨ s.sp.toNat + 16 ≤ (this + 132).toNat := by
    rw [h.toNat132]; have := h.disj; omega
  have h16 : (this + 16).toNat + 4 ≤ s.sp.toNat ∨ s.sp.toNat + 16 ≤ (this + 16).toNat := by
    rw [h.toNat16]; have := h.disj; omega
  obtain ⟨m', hr, hm⟩ := update_i_shape h dt limit isc
  have e : I' = Binary32.ofBits (w32 m' (this + 132).toNat) := by simp only [I', hr]
  rw [e]
  rcases hm with rfl | rfl | ⟨x, rfl⟩
  · exact Or.inl (by rw [hfr _ h132])
  · right; left
    rw [Corpus.Mem.w32_set4_self _ _ _ (by rw [hsz]; exact hin), Corpus.F32.ofBits_toBits]
  · right; right
    refine ⟨x, ?_⟩
    have hd : (this + 16).toNat + 4 ≤ (this + 132).toNat ∨ (this + 132).toNat + 4 ≤ (this + 16).toNat := by
      rw [h.toNat16, h.toNat132]; omega
    simp only [updMem]
    rw [Corpus.Mem.w32_set4_self _ _ _ (by rw [Corpus.Mem.size_set4, hsz]; exact hin), Corpus.F32.ofBits_toBits,
      Corpus.Mem.w32_set4_self _ _ _ (by rw [hsz]; exact hin), Corpus.F32.ofBits_toBits,
      Corpus.Mem.w32_set4_of_disjoint _ _ _ _ hd, hfr _ h16]
    rfl

/-- Invariant: if `0 ≤ kimax` (finite) and `-kimax ≤ integrator ≤ kimax` before the call, the same holds after it
(`kimax` itself is unchanged, `update_i_kimax`). -/
theorem update_i_preserves_bound {s : PMem.Mem} {this : UInt64} (h : Pre s this) (dt : Binary32) (limit : Bool)
    (isc : Binary32)
    (hMf : Binary32.isFinite (Binary32.ofBits (w32 s.m (this + 16).toNat)) = true)
    (hM0 : Binary32.ofBits 0x00000000 ≤ Binary32.ofBits (w32 s.m (this + 16).toNat))
    (hI : -Binary32.ofBits (w32 s.m (this + 16).toNat) ≤ Binary32.ofBits (w32 s.m (this + 132).toNat) ∧
      Binary32.ofBits (w32 s.m (this + 132).toNat) ≤ Binary32.ofBits (w32 s.m (this + 16).toNat)) :
    let s' := ((Vehicle_lib.AC_PID.update_i this dt limit isc).run s).2
    (-Binary32.ofBits (w32 s'.m (this + 16).toNat)) ≤ Binary32.ofBits (w32 s'.m (this + 132).toNat) ∧
      Binary32.ofBits (w32 s'.m (this + 132).toNat) ≤ Binary32.ofBits (w32 s'.m (this + 16).toNat) := by
  dsimp only
  rw [update_i_kimax h dt limit isc]
  have hint := update_i_integrator h dt limit isc
  dsimp only at hint
  generalize hMdef : Binary32.ofBits (w32 s.m (this + 16).toNat) = M at hMf hM0 hI hint
  rcases hint with e | e | ⟨x, e⟩ <;> rw [e]
  · exact hI
  · have hMn := (Corpus.F32.isNaN_false_of_le hM0).2
    refine ⟨?_, hM0⟩
    have hnn : Binary32.isNaN (-M) = false := by rw [Corpus.F32.isNaN_neg]; exact hMn
    have h0 := hM0
    rw [Corpus.F32.le_iff_ext hnn Corpus.F32.isNaN_zero, Corpus.F32.ext_neg hMn, Corpus.F32.ext_zero]
    rw [Corpus.F32.le_iff_ext Corpus.F32.isNaN_zero hMn, Corpus.F32.ext_zero] at h0
    exact EReal.neg_le_zero.2 h0
  · cases hx : Binary32.isNaN x
    · exact Corpus.AP_Math.constrain_float_mem _ (Corpus.F32.neg_le_self hM0) hx
    · rw [Corpus.AP_Math.constrain_float_of_isNaN _ _ _ hx]
      exact (Corpus.F32.midpoint_neg_self_mem hMf hM0).2

end Corpus.AC_PID

/-! ## `Pre` for the controller's `AC_PID` objects (second increment)

The vehicle's memory (`Vehicle_lib.initMem`) is `memSize = 0x40000` bytes: constant data and the static objects below
`heapBase = 0x20000` (the bridged range `[Bridge.lo, Bridge.hi) = [0x844d, 0x9f6a)` is among them, inside `copter`
at `0x86d8`), the heap `[heapBase, stackBase)` growing up from `0x20000` (`PMem.alloc`), the stack
`[stackBase, memSize)` growing up from `0x30000` (`PMem.enter`). The four `AC_PID` objects of the controller are
members of heap objects: `AC_AttitudeControl_Multi` (1112 bytes, `Copter::allocate_motors`, `PMem.alloc 1112`) holds
the rate PIDs at `+376`, `+616`, `+856` (`get_rate_roll_pid`, `get_rate_pitch_pid`, `get_rate_yaw_pid`), and
`AC_PosControl` (984 bytes, `PMem.alloc 984`) holds the vertical acceleration PID at `+384` (`D_get_accel_pid`). An
`AC_PID` is 240 bytes (the rate PIDs are 240 apart). No `Vehicle_lib.addr'…` constant names them: their addresses are
heap addresses chosen at initialization. So `Pre` is discharged from two region facts: the stack predicate, and the
owning object lying in the heap region. -/

namespace Corpus.AC_PID

open Corpus.Mem (InRegion StackOK)

/-- `Pre` for an `AC_PID` object (240 bytes) in the heap region, from the stack predicate with 16 bytes of headroom. -/
theorem pre_of_regions {s : PMem.Mem} {this : UInt64}
    (hst : StackOK s Vehicle_lib.stackBase Vehicle_lib.memSize 16)
    (hobj : InRegion s this Vehicle_lib.heapBase Vehicle_lib.stackBase 240) : Pre s this := by
  have hdisj := hobj.disjoint hst (le_refl _)
  refine ⟨hst.raw0 (le_refl _), (hst.raw0 (w := 4) (by omega)).bridge, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact hobj.raw (o := 4) (w := 4) (by omega)
  · exact hobj.raw (o := 16) (w := 4) (by omega)
  · exact hobj.raw (o := 132) (w := 4) (by omega)
  · exact hobj.raw (o := 140) (w := 4) (by omega)
  · have := hobj.nowrap; have := hobj.room
    simp only [Vehicle_lib.stackBase] at *; omega
  · right; omega

private theorem sub_obj {s : PMem.Mem} {a : UInt64} {lo hi n o : Nat} (h : InRegion s a lo hi n) (ho : o + 240 ≤ n) :
    InRegion s (a + o.toUInt64) lo hi 240 := by
  have e := h.toNat_add (o := o) (by omega)
  exact ⟨by rw [e]; have := h.lo_le; omega, by rw [e]; have := h.room; omega, h.inside, h.bridge, h.nowrap⟩

/-- The attitude controller's roll rate PID satisfies `Pre` (the attitude controller in the heap region). -/
theorem rate_roll_pid_pre {s : PMem.Mem} {att : UInt64}
    (hst : StackOK s Vehicle_lib.stackBase Vehicle_lib.memSize 16)
    (hatt : InRegion s att Vehicle_lib.heapBase Vehicle_lib.stackBase 1112) :
    Pre s (Id.run (Vehicle_lib.AC_AttitudeControl_Multi.get_rate_roll_pid.pure' att)) :=
  pre_of_regions hst (sub_obj (o := 376) hatt (by omega))

theorem rate_pitch_pid_pre {s : PMem.Mem} {att : UInt64}
    (hst : StackOK s Vehicle_lib.stackBase Vehicle_lib.memSize 16)
    (hatt : InRegion s att Vehicle_lib.heapBase Vehicle_lib.stackBase 1112) :
    Pre s (Id.run (Vehicle_lib.AC_AttitudeControl_Multi.get_rate_pitch_pid.pure' att)) :=
  pre_of_regions hst (sub_obj (o := 616) hatt (by omega))

theorem rate_yaw_pid_pre {s : PMem.Mem} {att : UInt64}
    (hst : StackOK s Vehicle_lib.stackBase Vehicle_lib.memSize 16)
    (hatt : InRegion s att Vehicle_lib.heapBase Vehicle_lib.stackBase 1112) :
    Pre s (Id.run (Vehicle_lib.AC_AttitudeControl_Multi.get_rate_yaw_pid.pure' att)) :=
  pre_of_regions hst (sub_obj (o := 856) hatt (by omega))

/-- The position controller's vertical acceleration PID satisfies `Pre` (the position controller in the heap region). -/
theorem accel_pid_pre {s : PMem.Mem} {pos : UInt64}
    (hst : StackOK s Vehicle_lib.stackBase Vehicle_lib.memSize 16)
    (hpos : InRegion s pos Vehicle_lib.heapBase Vehicle_lib.stackBase 984) :
    Pre s (Id.run (Vehicle_lib.AC_PosControl.D_get_accel_pid.pure' pos)) :=
  pre_of_regions hst (sub_obj (o := 384) hpos (by omega))

/-- The layout facts `pre_of_regions` relies on, checked on the constants: the bridged range ends below the heap, the
heap ends where the stack begins, the stack ends at the memory's size. -/
theorem layout_regions :
    PMem.Bridge.hi.toNat ≤ Vehicle_lib.heapBase ∧ Vehicle_lib.heapBase ≤ Vehicle_lib.stackBase ∧
      Vehicle_lib.stackBase ≤ Vehicle_lib.memSize ∧ Vehicle_lib.memSize < 2 ^ 64 := by
  decide

end Corpus.AC_PID

/-! ## `update_i`: the exact update (second increment) -/

namespace Corpus.AC_PID

/-- The value the update branch stores before clamping: `_integrator + ((_error * _ki) * i_scale) * dt`, the fields
read from the memory `m1` (the frame's memory; outside the frame it is the caller's). -/
abbrev xUpd (m1 : ByteArray) (this : UInt64) (isc dt : Binary32) : Binary32 :=
  Binary32.ofBits (w32 m1 (this + 132).toNat) +
    ((Binary32.ofBits (w32 m1 (this + 140).toNat) * Binary32.ofBits (w32 m1 (this + 4).toNat)) * isc) * dt

/-- The three shapes, the update branch with its exact value. -/
def ShapeX (s : PMem.Mem) (this : UInt64) (isc dt : Binary32) (r : Unit × PMem.Mem) : Prop :=
  ∃ m', r = ((), { s with m := m' }) ∧
    (m' = frameMem s.m this s.sp ∨
      m' = set4 (frameMem s.m this s.sp) (this + 132).toNat (Binary32.toBits (Binary32.ofBits 0x00000000)) ∨
      m' = updMem (frameMem s.m this s.sp) this (xUpd (frameMem s.m this s.sp) this isc dt))

def BodyShapeX (s : PMem.Mem) (this : UInt64) (isc dt : Binary32) (r : Unit × PMem.Mem) : Prop :=
  ∃ m', r = ((), { s with sp := s.sp + 16, m := m' }) ∧
    (m' = frameMem s.m this s.sp ∨
      m' = set4 (frameMem s.m this s.sp) (this + 132).toNat (Binary32.toBits (Binary32.ofBits 0x00000000)) ∨
      m' = updMem (frameMem s.m this s.sp) this (xUpd (frameMem s.m this s.sp) this isc dt))

private theorem BodyShapeX.ite {s : PMem.Mem} {this : UInt64} {isc dt : Binary32} {c : Prop} [Decidable c]
    {a b : Unit × PMem.Mem} (ha : BodyShapeX s this isc dt a) (hb : BodyShapeX s this isc dt b) :
    BodyShapeX s this isc dt (if c then a else b) := by
  split <;> assumption

private theorem BodyShapeX.leave {s : PMem.Mem} {this : UInt64} {isc dt : Binary32} {r : Unit × PMem.Mem}
    (hr : BodyShapeX s this isc dt r) : ShapeX s this isc dt (r.1, { r.2 with sp := s.sp }) := by
  obtain ⟨m', rfl, hm⟩ := hr
  exact ⟨m', rfl, hm⟩

/-- Effect/Case: `update_i` leaves the state in one of the three shapes, the update branch storing
`constrain_float(_integrator + ((_error * _ki) * i_scale) * dt, -_kimax, _kimax)`. -/
theorem update_i_shape_exact {s : PMem.Mem} {this : UInt64} (h : Pre s this) (dt : Binary32) (limit : Bool)
    (isc : Binary32) : ShapeX s this isc dt ((Vehicle_lib.AC_PID.update_i this dt limit isc).run s) := by
  have hsp0 : s.sp + 0 = s.sp := by simp
  have hsz0 : (PMem.zeroBlock.copySlice 0 s.m s.sp.toNat 16).size = s.m.size :=
    Corpus.Mem.size_copySlice _ _ _ _ _ h.frame.inside (by rw [Corpus.Mem.zeroBlock_size]; omega)
  have hd : Raw { s with sp := s.sp + 16, m := PMem.zeroBlock.copySlice 0 s.m s.sp.toNat 16 } (s.sp + 0) 4 :=
    ⟨by rw [hsp0]; exact h.fp, by rw [hsp0]; simp only [hsz0]; have := h.frame.inside; omega,
     by rw [hsp0]; have := h.frame.nowrap; omega⟩
  have hs : Raw { s with sp := s.sp + 16, m := PMem.zeroBlock.copySlice 0 s.m s.sp.toNat 16 } (this + 4) 4 :=
    ⟨h.ki.bridge, by simp only [hsz0]; exact h.ki.inside, h.ki.nowrap⟩
  have hdisj : (s.sp + 0).toNat + 4 ≤ (this + 4).toNat ∨ (this + 4).toNat + 4 ≤ (s.sp + 0).toNat := by
    rw [hsp0, h.toNat4]; have := h.disj; omega
  unfold Vehicle_lib.AC_PID.update_i
  rw [StateT.run_bind, Corpus.Mem.enter4_run h.frame]
  simp only [Corpus.id_bind, Corpus.id_run_eq]
  rw [StateT.run_bind]
  unfold Vehicle_lib.AC_PID.update_i.body
  simp only [StateT.run_bind, Corpus.Mem.discard_run, Corpus.Mem.memcpy4_run hd hs hdisj]
  simp only [Corpus.id_bind, Corpus.id_run_eq, StateT.run_bind, hsp0,
    Corpus.AP_Math.is_zero_param_run h.fp, Corpus.AP_Math.is_positive_eq, Corpus.AP_Math.is_negative_eq,
    Corpus.Mem.ldF32_run h.integ.bridge, Corpus.Mem.ldF32_run h.err.bridge, Corpus.Mem.ldF32_run h.ki.bridge,
    Corpus.Mem.ldF32_run h.kimax.bridge, Corpus.Mem.stF32_run h.integ.bridge h.integ.nowrap,
    Corpus.AP_Param.operator_const_float_run, Corpus.AP_Param.operator_neg_run h.kimax.bridge,
    Corpus.AP_Math.constrain_float_eq, StateT.run_pure, Corpus.Mem.leave_run, Corpus.Mem.run_ite,
    Corpus.Mem.discard_run, Corpus.id_pure_eq]
  rw [show ((PMem.zeroBlock.copySlice 0 s.m s.sp.toNat 16).extract (this + 4).toNat
      ((this + 4).toNat + 4)).copySlice 0 (PMem.zeroBlock.copySlice 0 s.m s.sp.toNat 16) s.sp.toNat 4 =
      frameMem s.m this s.sp from rfl]
  clear hd hs hdisj hsz0 hsp0
  generalize Vehicle_lib.is_zero.pure' = Z
  generalize Vehicle_lib.is_positive'float.pure' = P
  generalize Vehicle_lib.is_negative'float.pure' = N
  apply BodyShapeX.leave
  repeat
    first
    | exact ⟨_, by with_reducible rfl, Or.inl (by with_reducible rfl)⟩
    | exact ⟨_, by with_reducible rfl, Or.inr (Or.inl (by with_reducible rfl))⟩
    | exact ⟨_, by with_reducible rfl, Or.inr (Or.inr (by with_reducible rfl))⟩
    | apply BodyShapeX.ite

private theorem frameMem_w32 {s : PMem.Mem} {this : UInt64} (h : Pre s this) {a : Nat}
    (ha : a + 4 ≤ s.sp.toNat ∨ s.sp.toNat + 16 ≤ a) : w32 (frameMem s.m this s.sp) a = w32 s.m a := by
  unfold w32
  rw [frameMem_get! h (by omega), frameMem_get! h (by omega), frameMem_get! h (by omega),
    frameMem_get! h (by omega)]

/-- Case/Effect: the integrator after the call is the integrator before (no update), `0`, or, in the update branch,
exactly `constrain_float(integrator + ((error * ki) * i_scale) * dt, -kimax, kimax)`, every field read before the
call. -/
theorem update_i_integrator_exact {s : PMem.Mem} {this : UInt64} (h : Pre s this) (dt : Binary32) (limit : Bool)
    (isc : Binary32) :
    let I' := Binary32.ofBits (w32 ((Vehicle_lib.AC_PID.update_i this dt limit isc).run s).2.m (this + 132).toNat)
    let I := Binary32.ofBits (w32 s.m (this + 132).toNat)
    let E := Binary32.ofBits (w32 s.m (this + 140).toNat)
    let K := Binary32.ofBits (w32 s.m (this + 4).toNat)
    let M := Binary32.ofBits (w32 s.m (this + 16).toNat)
    I' = I ∨ I' = Binary32.ofBits 0x00000000 ∨
      I' = Id.run (Vehicle_lib.constrain_value_line'float.pure' (I + ((E * K) * isc) * dt) (-M) M
        (Int32.toUInt32 346)) := by
  intro I' I E K M
  have hsz := frameMem_size h
  have hin := h.integ.inside
  have h132 : (this + 132).toNat + 4 ≤ s.sp.toNat ∨ s.sp.toNat + 16 ≤ (this + 132).toNat := by
    rw [h.toNat132]; have := h.disj; omega
  have h16 : (this + 16).toNat + 4 ≤ s.sp.toNat ∨ s.sp.toNat + 16 ≤ (this + 16).toNat := by
    rw [h.toNat16]; have := h.disj; omega
  have h140 : (this + 140).toNat + 4 ≤ s.sp.toNat ∨ s.sp.toNat + 16 ≤ (this + 140).toNat := by
    rw [h.toNat140]; have := h.disj; omega
  have h4 : (this + 4).toNat + 4 ≤ s.sp.toNat ∨ s.sp.toNat + 16 ≤ (this + 4).toNat := by
    rw [h.toNat4]; have := h.disj; omega
  obtain ⟨m', hr, hm⟩ := update_i_shape_exact h dt limit isc
  have e : I' = Binary32.ofBits (w32 m' (this + 132).toNat) := by simp only [I', hr]
  rw [e]
  rcases hm with rfl | rfl | rfl
  · exact Or.inl (by rw [frameMem_w32 h h132])
  · right; left
    rw [Corpus.Mem.w32_set4_self _ _ _ (by rw [hsz]; exact hin), Corpus.F32.ofBits_toBits]
  · right; right
    have hd : (this + 16).toNat + 4 ≤ (this + 132).toNat ∨ (this + 132).toNat + 4 ≤ (this + 16).toNat := by
      rw [h.toNat16, h.toNat132]; omega
    simp only [updMem, xUpd]
    rw [Corpus.Mem.w32_set4_self _ _ _ (by rw [Corpus.Mem.size_set4, hsz]; exact hin), Corpus.F32.ofBits_toBits,
      Corpus.Mem.w32_set4_self _ _ _ (by rw [hsz]; exact hin), Corpus.F32.ofBits_toBits,
      Corpus.Mem.w32_set4_of_disjoint _ _ _ _ hd, frameMem_w32 h h16, frameMem_w32 h h132, frameMem_w32 h h140,
      frameMem_w32 h h4]
    rfl

end Corpus.AC_PID

/-! ## The filter coefficients (callees of `update_all`) -/

namespace Corpus.AC_PID

/-- C++ `AC_PID::get_filt_T_alpha : float (float) const`, `AC_PID.cpp:415-418`: `calc_lowpass_alpha_dt(dt,
_filt_T_hz)`, `_filt_T_hz` at `+24`; the memory unchanged. -/
theorem get_filt_T_alpha_run {this : UInt64} (hb : PMem.inBridgeN (this + 24) 4 = false) (dt : Binary32)
    (s : PMem.Mem) :
    (Vehicle_lib.AC_PID.get_filt_T_alpha this dt).run s =
      (Vehicle_lib.calc_lowpass_alpha_dt dt (Binary32.ofBits (w32 s.m (this + 24).toNat))).run s := by
  unfold Vehicle_lib.AC_PID.get_filt_T_alpha
  simp only [StateT.run_bind, Corpus.AP_Param.operator_const_float_run, Corpus.id_bind, Corpus.id_run_eq,
    Corpus.Mem.ldF32_run hb, Corpus.AP_Math.calc_lowpass_alpha_dt_run]

/-- C++ `AC_PID::get_filt_E_alpha : float (float) const`, `AC_PID.cpp:421-424`: `_filt_E_hz` at `+28`. -/
theorem get_filt_E_alpha_run {this : UInt64} (hb : PMem.inBridgeN (this + 28) 4 = false) (dt : Binary32)
    (s : PMem.Mem) :
    (Vehicle_lib.AC_PID.get_filt_E_alpha this dt).run s =
      (Vehicle_lib.calc_lowpass_alpha_dt dt (Binary32.ofBits (w32 s.m (this + 28).toNat))).run s := by
  unfold Vehicle_lib.AC_PID.get_filt_E_alpha
  simp only [StateT.run_bind, Corpus.AP_Param.operator_const_float_run, Corpus.id_bind, Corpus.id_run_eq,
    Corpus.Mem.ldF32_run hb, Corpus.AP_Math.calc_lowpass_alpha_dt_run]

/-- C++ `AC_PID::get_filt_D_alpha : float (float) const`, `AC_PID.cpp:427-430`: `_filt_D_hz` at `+32`. -/
theorem get_filt_D_alpha_run {this : UInt64} (hb : PMem.inBridgeN (this + 32) 4 = false) (dt : Binary32)
    (s : PMem.Mem) :
    (Vehicle_lib.AC_PID.get_filt_D_alpha this dt).run s =
      (Vehicle_lib.calc_lowpass_alpha_dt dt (Binary32.ofBits (w32 s.m (this + 32).toNat))).run s := by
  unfold Vehicle_lib.AC_PID.get_filt_D_alpha
  simp only [StateT.run_bind, Corpus.AP_Param.operator_const_float_run, Corpus.id_bind, Corpus.id_run_eq,
    Corpus.Mem.ldF32_run hb, Corpus.AP_Math.calc_lowpass_alpha_dt_run]

end Corpus.AC_PID

/-! ## `update_i` as a step of a caller (third increment) -/

namespace Corpus.AC_PID

open Corpus.Hoare (Agree Ival Inv Triple WOk Stable)

theorem update_i_size {s : PMem.Mem} {this : UInt64} (h : Pre s this) (dt : Binary32) (limit : Bool)
    (isc : Binary32) : ((Vehicle_lib.AC_PID.update_i this dt limit isc).run s).2.m.size = s.m.size := by
  obtain ⟨m', hr, hm⟩ := update_i_shape h dt limit isc
  rw [hr]
  rcases hm with rfl | rfl | ⟨x, rfl⟩
  · exact frameMem_size h
  · simp only [Corpus.Mem.size_set4]; exact frameMem_size h
  · simp only [updMem, Corpus.Mem.size_set4]; exact frameMem_size h

/-- Effect, in the `Agree` form a caller uses: `update_i` changes only `_integrator` (`[this + 132, this + 136)`) and
its frame (`[sp, sp + 16)`). -/
theorem update_i_agree {s : PMem.Mem} {this : UInt64} (h : Pre s this) (dt : Binary32) (limit : Bool)
    (isc : Binary32) :
    Agree s ((Vehicle_lib.AC_PID.update_i this dt limit isc).run s).2
      (fun j => Ival (this.toNat + 132) 4 j ∨ Ival s.sp.toNat 16 j) := by
  refine ⟨update_i_size h dt limit isc, fun j hj => ?_, ?_⟩
  · simp only [Ival, not_or, not_and, not_lt] at hj
    exact (update_i_frame h dt limit isc (j := j) (by rw [h.toNat132]; omega) (by omega)).2
  · obtain ⟨m', hr, _⟩ := update_i_shape h dt limit isc
    rw [hr]

end Corpus.AC_PID

namespace Corpus.AC_PID

open Corpus.Hoare (Triple)

/-- `get_filt_T_alpha` reads and writes nothing: every precondition is kept. -/
theorem get_filt_T_alpha_triple {P : PMem.Mem → Prop} {this : UInt64} (hb : PMem.inBridgeN (this + 24) 4 = false)
    (dt : Binary32) : Triple P (Vehicle_lib.AC_PID.get_filt_T_alpha this dt) (fun _ => P) :=
  Corpus.Hoare.Triple.of_state fun s =>
    congrArg Prod.snd ((get_filt_T_alpha_run hb dt s).trans (Corpus.Filter.calc_lowpass_alpha_dt_run' _ _ s))

theorem get_filt_E_alpha_triple {P : PMem.Mem → Prop} {this : UInt64} (hb : PMem.inBridgeN (this + 28) 4 = false)
    (dt : Binary32) : Triple P (Vehicle_lib.AC_PID.get_filt_E_alpha this dt) (fun _ => P) :=
  Corpus.Hoare.Triple.of_state fun s =>
    congrArg Prod.snd ((get_filt_E_alpha_run hb dt s).trans (Corpus.Filter.calc_lowpass_alpha_dt_run' _ _ s))

theorem get_filt_D_alpha_triple {P : PMem.Mem → Prop} {this : UInt64} (hb : PMem.inBridgeN (this + 32) 4 = false)
    (dt : Binary32) : Triple P (Vehicle_lib.AC_PID.get_filt_D_alpha this dt) (fun _ => P) :=
  Corpus.Hoare.Triple.of_state fun s =>
    congrArg Prod.snd ((get_filt_D_alpha_run hb dt s).trans (Corpus.Filter.calc_lowpass_alpha_dt_run' _ _ s))

end Corpus.AC_PID

/-! ## `AC_PID::update_all`: Effect and the integrator bound (third increment)

C++ `AC_PID::update_all : float (float, float, float, bool, float, float)`, `AC_PID.cpp:196-311`. Its stores, all
inside `[this + 48, this + 200)`: the slew limiter at `+48` (through `SlewLimiter::modifier`, `[this + 64,
this + 126)`), the flags' bit-field at `+128` (`_reset_filter` bit 0, `_I_term_set` bit 1), `_integrator` at `+132`
(through `update_i`), `_target` `+136`, `_error` `+140`, `_derivative` `+144`, `_target_derivative` `+152`, and
`_pid_info` at `+156 … +199`; the stack from its frame on: its own 16 bytes, then `update_i`'s, `modifier`'s and
`LowPassFilter::apply`'s (48 bytes in all). `_kimax` (`+16`) and `_integrator` are written by nothing but `update_i`. -/

namespace Corpus.AC_PID

open Corpus.Mem (w32 set4 Raw)
open Corpus.Hoare (Agree Ival Inv Triple WOk Stable)

/-- The bytes `update_all`'s body may write: the object from `+48` to `+200`, and 48 bytes of stack from its frame. -/
abbrev updW (this fp : UInt64) (j : Nat) : Prop := Ival (this.toNat + 48) 152 j ∨ Ival fp.toNat 48 j

/-- `_kimax` and `_integrator`: written by `update_i` alone. -/
abbrev updV (this : UInt64) (j : Nat) : Prop := Ival (this.toNat + 16) 4 j ∨ Ival (this.toNat + 132) 4 j

/-- The body's hypotheses on its entry state `s₁`: the `AC_PID` object (240 bytes) and 48 bytes of stack from the
frame `fp` are raw, above the bridged range, disjoint; the stack pointer is past the frame. -/
structure UBody (s₁ : PMem.Mem) (this fp : UInt64) : Prop where
  obj : Raw s₁ this 240
  objHi : PMem.Bridge.hi.toNat ≤ this.toNat
  stk : Raw s₁ fp 48
  stkHi : PMem.Bridge.hi.toNat ≤ fp.toNat
  disj : fp.toNat + 48 ≤ this.toNat ∨ this.toNat + 240 ≤ fp.toNat
  sp : s₁.sp = fp + 16

private theorem UBody.wok {s₁ : PMem.Mem} {this fp : UInt64} (h : UBody s₁ this fp) :
    WOk s₁ (fun j => Ival (this.toNat + 48) 152 j ∨ Ival fp.toNat 48 j) := by
  have := h.obj.inside; have := h.stk.inside; have := h.objHi; have := h.stkHi
  have := h.obj.nowrap; have := h.stk.nowrap
  exact ⟨fun j hj => by simp only [Ival] at hj; omega⟩

private theorem toNat_off {a : UInt64} {n o : Nat} (hn : a.toNat + n < 2 ^ 64) (ho : o ≤ n) :
    (a + o.toUInt64).toNat = a.toNat + o := by
  rw [UInt64.toNat_add, Corpus.Mem.toNat_toUInt64_of_lt (by omega)]; omega

/-- `Pre` (of `update_i`) at every invariant state of `update_all`'s body. -/
private theorem UBody.pre {s₁ s : PMem.Mem} {this fp : UInt64} {W V : Nat → Prop} {R : PMem.Mem → Prop}
    (h : UBody s₁ this fp) (hs : Inv s₁ W V R s) : Pre s this := by
  have hsz := hs.agree.size
  have hsp : s.sp = fp + 16 := by rw [hs.agree.sp, h.sp]
  have ho := h.obj.nowrap; have hf := h.stk.nowrap
  have ef : (fp + 16).toNat = fp.toNat + 16 := toNat_off (o := 16) (n := 48) hf (by omega)
  have fr0 := h.stk.sub (o := 16) (w := 16) (by omega) (by omega)
  have fr : Raw s s.sp 16 := by rw [hsp]; exact fr0.congr hsz
  refine ⟨fr, (by simpa using fr.sub (o := 0) (w := 4) (by omega) (by omega) : Raw s s.sp 4).bridge,
    (h.obj.sub (o := 4) (w := 4) (by omega) (by omega)).congr hsz,
    (h.obj.sub (o := 16) (w := 4) (by omega) (by omega)).congr hsz,
    (h.obj.sub (o := 132) (w := 4) (by omega) (by omega)).congr hsz,
    (h.obj.sub (o := 140) (w := 4) (by omega) (by omega)).congr hsz, by omega, ?_⟩
  rw [hsp, ef]; have := h.disj; omega

/-- The call of `update_i` keeps the body's invariant, when `update_i` keeps `R`. -/
theorem update_all_update_i_call {s₁ : PMem.Mem} {this fp : UInt64} (h : UBody s₁ this fp) {R : PMem.Mem → Prop}
    (dt : Binary32) (limit : Bool) (i_scale : Binary32)
    (hRi : ∀ s, Pre s this → R s → R ((Vehicle_lib.AC_PID.update_i this dt limit i_scale).run s).2) :
    Triple (Inv s₁ (fun j => Ival (this.toNat + 48) 152 j ∨ Ival fp.toNat 48 j)
        (fun j => Ival (this.toNat + 16) 4 j ∨ Ival (this.toNat + 132) 4 j) R)
      (Vehicle_lib.AC_PID.update_i this dt limit i_scale)
      (fun _ => Inv s₁ (fun j => Ival (this.toNat + 48) 152 j ∨ Ival fp.toNat 48 j)
        (fun j => Ival (this.toNat + 16) 4 j ∨ Ival (this.toNat + 132) 4 j) R) := fun s hs => by
  have pre := h.pre hs
  have hsp : s.sp = fp + 16 := by rw [hs.agree.sp, h.sp]
  have hf := h.stk.nowrap
  have ef : (fp + 16).toNat = fp.toNat + 16 := toNat_off (o := 16) (n := 48) hf (by omega)
  refine ⟨hs.agree.trans ((update_i_agree pre dt limit i_scale).mono ?_), hRi s pre hs.r⟩
  intro j hj
  rw [hsp, ef] at hj
  simp only [Ival] at hj ⊢; omega

/-- The call of `SlewLimiter::modifier` on the slew limiter (`this + 48`) keeps the body's invariant. -/
theorem update_all_modifier_call {s₁ : PMem.Mem} {this fp : UInt64} (h : UBody s₁ this fp) {R : PMem.Mem → Prop}
    (hR : Stable R (fun j => Ival (this.toNat + 16) 4 j ∨ Ival (this.toNat + 132) 4 j)) (x dt : Binary32) :
    Triple (Inv s₁ (fun j => Ival (this.toNat + 48) 152 j ∨ Ival fp.toNat 48 j)
        (fun j => Ival (this.toNat + 16) 4 j ∨ Ival (this.toNat + 132) 4 j) R)
      (Vehicle_lib.SlewLimiter.modifier (this + 48) x dt)
      (fun _ => Inv s₁ (fun j => Ival (this.toNat + 48) 152 j ∨ Ival fp.toNat 48 j)
        (fun j => Ival (this.toNat + 16) 4 j ∨ Ival (this.toNat + 132) 4 j) R) := by
  have ho := h.obj.nowrap; have hf := h.stk.nowrap
  have e48 : (this + 48).toNat = this.toNat + 48 := toNat_off (o := 48) (n := 240) ho (by omega)
  have ef : (fp + 16).toNat = fp.toNat + 16 := toNat_off (o := 16) (n := 48) hf (by omega)
  refine Corpus.Hoare.Triple.call hR (X := fun j => Ival (this.toNat + 64) 62 j ∨ Ival (fp.toNat + 16) 32 j)
    (fun s hs => ?_) ?_
  · have hsz := hs.agree.size
    have hsp : s.sp = fp + 16 := by rw [hs.agree.sp, h.sp]
    have o0 := h.obj.sub (o := 48) (w := 78) (by omega) (by omega)
    have s0 := h.stk.sub (o := 16) (w := 32) (by omega) (by omega)
    have pre : Corpus.Filter.ModPre s (this + 48) := by
      refine ⟨o0.congr hsz, by rw [e48]; have := h.objHi; omega, by rw [hsp]; exact s0.congr hsz,
        by rw [hsp, ef]; have := h.stkHi; omega, by rw [hsp, ef, e48]; have := h.disj; omega⟩
    have := Corpus.Filter.modifier_agree pre x dt
    rw [hsp, ef, e48] at this
    exact this.mono (fun j hj => by simp only [Ival] at hj ⊢; omega)
  · have hd := h.disj
    intro j hj; simp only [Ival, not_or, not_and, not_lt] at hj ⊢; omega

theorem update_all_body_triple {s₁ : PMem.Mem} {this fp : UInt64} (target measurement dt : Binary32) (limit : Bool)
    (pd_scale i_scale : Binary32) (h : UBody s₁ this fp) {R : PMem.Mem → Prop}
    (hR : Stable R (fun j => Ival (this.toNat + 16) 4 j ∨ Ival (this.toNat + 132) 4 j))
    (hRi : ∀ s, Pre s this → R s → R ((Vehicle_lib.AC_PID.update_i this dt limit i_scale).run s).2) :
    Triple (Inv s₁ (fun j => Ival (this.toNat + 48) 152 j ∨ Ival fp.toNat 48 j)
        (fun j => Ival (this.toNat + 16) 4 j ∨ Ival (this.toNat + 132) 4 j) R)
      (Vehicle_lib.AC_PID.update_all.body fp this target measurement dt limit pd_scale i_scale)
      (fun _ => Inv s₁ (fun j => Ival (this.toNat + 48) 152 j ∨ Ival fp.toNat 48 j)
        (fun j => Ival (this.toNat + 16) 4 j ∨ Ival (this.toNat + 132) 4 j) R) := by
  have hW := h.wok
  have ho := h.obj.nowrap
  have hf := h.stk.nowrap
  have hd := h.disj
  have hraw : ∀ o, o + 4 ≤ 240 → PMem.inBridgeN (this + o.toUInt64) 4 = false :=
    fun o ho' => (h.obj.sub (o := o) (w := 4) ho' (by omega)).bridge
  have hb12 : PMem.inBridgeN (this + 24) 4 = false := hraw 24 (by omega)
  have hb13 : PMem.inBridgeN (this + 28) 4 = false := hraw 28 (by omega)
  have hb14 : PMem.inBridgeN (this + 32) 4 = false := hraw 32 (by omega)
  have hb76 : PMem.inBridgeN (this + 48 + 28) 4 = false := by
    have := hraw 76 (by omega); rwa [UInt64.add_assoc]
  have hbfp : PMem.inBridgeN (fp + 0) 4 = false := by
    simpa using (h.stk.sub (o := 0) (w := 4) (by omega) (by omega)).bridge
  have h20 : Raw s₁ (this + 20) 4 := h.obj.sub (o := 20) (w := 4) (by omega) (by omega)
  unfold Vehicle_lib.AC_PID.update_all.body
  repeat' triple_step
  all_goals first
    | sub_tac
    | with_reducible exact update_all_update_i_call h dt limit i_scale hRi
    | with_reducible exact update_all_modifier_call h hR _ _
    | with_reducible exact Corpus.Hoare.Triple.of_pure (Corpus.AP_Math.is_positive_eq _)
    | with_reducible exact Corpus.AP_Param.operator_const_float_triple _
    | with_reducible exact get_filt_T_alpha_triple hb12 dt
    | with_reducible exact get_filt_E_alpha_triple hb13 dt
    | with_reducible exact get_filt_D_alpha_triple hb14 dt
    | with_reducible exact Corpus.Filter.get_slew_rate_triple hb76
    | with_reducible exact Corpus.AP_Math.is_positive_param_triple hbfp
    | (refine Corpus.Hoare.Triple.memcpy' hR hW (by decide) (by sub_tac) h20 ?_
       simp only [UInt64.toNat_add, UInt64.reduceToNat]; omega)

/-- The hypotheses of `update_all`: the `AC_PID` object (240 bytes) and 48 bytes of stack from the stack pointer are
raw, above the bridged range, and disjoint. -/
structure UPre (s : PMem.Mem) (this : UInt64) : Prop where
  obj : Raw s this 240
  objHi : PMem.Bridge.hi.toNat ≤ this.toNat
  stk : Raw s s.sp 48
  stkHi : PMem.Bridge.hi.toNat ≤ s.sp.toNat
  disj : s.sp.toNat + 48 ≤ this.toNat ∨ this.toNat + 240 ≤ s.sp.toNat

/-- The body run from the entered state, for any property `R` that writes outside `_kimax`/`_integrator` keep and
that `update_i` keeps. -/
private theorem update_all_run_inv {s : PMem.Mem} {this : UInt64} (h : UPre s this) (target measurement dt : Binary32)
    (limit : Bool) (pd_scale i_scale : Binary32) {R : PMem.Mem → Prop}
    (hR : Stable R (fun j => Ival (this.toNat + 16) 4 j ∨ Ival (this.toNat + 132) 4 j))
    (hRi : ∀ s, Pre s this → R s → R ((Vehicle_lib.AC_PID.update_i this dt limit i_scale).run s).2)
    (hR0 : R s) :
    Agree s ((Vehicle_lib.AC_PID.update_all this target measurement dt limit pd_scale i_scale).run s).2
        (fun j => Ival (this.toNat + 48) 152 j ∨ Ival s.sp.toNat 48 j) ∧
      R ((Vehicle_lib.AC_PID.update_all this target measurement dt limit pd_scale i_scale).run s).2 := by
  have h16 : Raw s s.sp (Corpus.Mem.frameSize 4) := by
    simpa using h.stk.sub (o := 0) (w := 16) (by omega) (by omega)
  have hen := Corpus.Mem.enter_run (s := s) (k := 4) (by omega) (by decide) h16
  have hsz := Corpus.Mem.size_enter s.m s.sp.toNat 16 (by have := h.stk.inside; omega) (by omega)
  have hub : UBody ((PMem.enter 4).run s).2 this s.sp := by
    rw [hen]
    exact ⟨h.obj.congr hsz, h.objHi, h.stk.congr hsz, h.stkHi, h.disj, rfl⟩
  rw [hen] at hub
  have hd := h.disj
  have hR1 : R ((PMem.enter 4).run s).2 := by
    rw [hen]
    refine hR _ _ hR0 hsz (fun j hj => ?_)
    simp only [Ival] at hj
    have hfs : Corpus.Mem.frameSize 4 = 16 := rfl
    rw [hfs]
    exact Corpus.Mem.get!_enter _ _ _ _ (by have := h.stk.inside; omega) (by omega) (by omega)
  rw [hen] at hR1
  have hb := update_all_body_triple target measurement dt limit pd_scale i_scale hub hR hRi _ ⟨Agree.refl _ _, hR1⟩
  unfold Vehicle_lib.AC_PID.update_all
  rw [Corpus.Mem.run_bind', hen]
  simp only [Corpus.Mem.run_bind']
  refine ⟨Agree.frame hb.agree (by have := h.stk.inside; show s.sp.toNat + 16 ≤ _; omega) (by decide)
    (fun j hj => Or.inr ⟨hj.1, by have := hj.2; unfold Corpus.Mem.frameSize at this; omega⟩), ?_⟩
  exact hR _ _ hb.r rfl (fun _ _ => rfl)

/-- Effect: `AC_PID::update_all` changes only the bytes `[this + 48, this + 200)` of the object (the slew limiter,
the flags, `_integrator`, the filtered target, error and derivatives, `_pid_info`) and the 48 bytes of stack from the
stack pointer (its frame and its callees'); the stack pointer and every other part of the state are as before. -/
theorem update_all_agree {s : PMem.Mem} {this : UInt64} (h : UPre s this) (target measurement dt : Binary32)
    (limit : Bool) (pd_scale i_scale : Binary32) :
    Agree s ((Vehicle_lib.AC_PID.update_all this target measurement dt limit pd_scale i_scale).run s).2
      (fun j => Ival (this.toNat + 48) 152 j ∨ Ival s.sp.toNat 48 j) :=
  (update_all_run_inv h target measurement dt limit pd_scale i_scale (Corpus.Hoare.stable_true _)
    (fun _ _ _ => trivial) trivial).1

/-- The integrator bound of an `AC_PID` object: `_kimax` (`+16`) finite and `≥ 0`, and
`-_kimax ≤ _integrator ≤ _kimax` (`+132`). -/
def IBound (this : UInt64) (s : PMem.Mem) : Prop :=
  Binary32.isFinite (Binary32.ofBits (w32 s.m (this + 16).toNat)) = true ∧
    Binary32.ofBits 0x00000000 ≤ Binary32.ofBits (w32 s.m (this + 16).toNat) ∧
    -Binary32.ofBits (w32 s.m (this + 16).toNat) ≤ Binary32.ofBits (w32 s.m (this + 132).toNat) ∧
    Binary32.ofBits (w32 s.m (this + 132).toNat) ≤ Binary32.ofBits (w32 s.m (this + 16).toNat)

private theorem IBound.stable {this : UInt64} (ho : this.toNat + 240 < 2 ^ 64) :
    Stable (IBound this) (fun j => Ival (this.toNat + 16) 4 j ∨ Ival (this.toNat + 132) 4 j) := by
  intro s s' hb hsz ha
  have e16 : (this + 16).toNat = this.toNat + 16 := toNat_off (o := 16) (n := 240) ho (by omega)
  have e132 : (this + 132).toNat = this.toNat + 132 := toNat_off (o := 132) (n := 240) ho (by omega)
  have w16 : w32 s'.m (this + 16).toNat = w32 s.m (this + 16).toNat := by
    unfold w32; rw [e16]
    rw [ha _ (Or.inl ⟨by omega, by omega⟩), ha _ (Or.inl ⟨by omega, by omega⟩), ha _ (Or.inl ⟨by omega, by omega⟩),
      ha _ (Or.inl ⟨by omega, by omega⟩)]
  have w132 : w32 s'.m (this + 132).toNat = w32 s.m (this + 132).toNat := by
    unfold w32; rw [e132]
    rw [ha _ (Or.inr ⟨by omega, by omega⟩), ha _ (Or.inr ⟨by omega, by omega⟩), ha _ (Or.inr ⟨by omega, by omega⟩),
      ha _ (Or.inr ⟨by omega, by omega⟩)]
  unfold IBound; rw [w16, w132]; exact hb

theorem update_i_preserves_ibound {s : PMem.Mem} {this : UInt64} (h : Pre s this) (dt : Binary32) (limit : Bool)
    (isc : Binary32) (hb : IBound this s) :
    IBound this ((Vehicle_lib.AC_PID.update_i this dt limit isc).run s).2 := by
  have hk := update_i_kimax h dt limit isc
  have hp := update_i_preserves_bound h dt limit isc hb.1 hb.2.1 hb.2.2
  unfold IBound; rw [hk]
  exact ⟨hb.1, hb.2.1, by rw [← hk]; exact hp.1, by rw [← hk]; exact hp.2⟩

/-- Invariant: `AC_PID::update_all` keeps the integrator bound `-_kimax ≤ _integrator ≤ _kimax` (with `_kimax` finite
and `≥ 0`): the only store into `_integrator` is `update_i`'s clamp, and nothing writes `_kimax`. -/
theorem update_all_preserves_bound {s : PMem.Mem} {this : UInt64} (h : UPre s this) (target measurement dt : Binary32)
    (limit : Bool) (pd_scale i_scale : Binary32) (hb : IBound this s) :
    IBound this ((Vehicle_lib.AC_PID.update_all this target measurement dt limit pd_scale i_scale).run s).2 :=
  (update_all_run_inv h target measurement dt limit pd_scale i_scale (IBound.stable h.obj.nowrap)
    (fun _ hp hb' => update_i_preserves_ibound hp dt limit i_scale hb') hb).2

end Corpus.AC_PID

/-! ## `UPre` from the region facts -/

namespace Corpus.AC_PID

open Corpus.Mem (InRegion StackOK)

/-- `UPre` (of `update_all`) for an `AC_PID` object in the heap region, from the stack predicate with 48 bytes of
headroom. -/
theorem upre_of_regions {s : PMem.Mem} {this : UInt64}
    (hst : StackOK s Vehicle_lib.stackBase Vehicle_lib.memSize 48)
    (hobj : InRegion s this Vehicle_lib.heapBase Vehicle_lib.stackBase 240) : UPre s this := by
  have hdisj := hobj.disjoint hst (le_refl _)
  have hb := hobj.bridge; have hl := hobj.lo_le; have hl' := hst.lo_le
  exact ⟨hobj.raw0 (le_refl _), by omega, hst.raw0 (le_refl _),
    by simp only [Vehicle_lib.stackBase, Vehicle_lib.heapBase] at *; omega, Or.inr hdisj⟩

end Corpus.AC_PID

/-! ## `update_i`: which condition selects which value (third increment) -/

namespace Corpus.AC_PID

/-- Case: which condition selects each of `update_i`'s three integrator values (`update_i_integrator_exact`). With
`K = _ki`, `I = _integrator`, `E = _error`, `M = _kimax` read before the call: the update branch runs when
`!is_zero(K) && is_positive(dt)` and (`!limit` or the integrator and the error have opposite signs), and stores the
clamped update; with `!is_zero(K) && is_positive(dt)` but neither, the integrator is unchanged; otherwise it is
zeroed. -/
theorem update_i_integrator_cases {s : PMem.Mem} {this : UInt64} (h : Pre s this) (dt : Binary32) (limit : Bool)
    (isc : Binary32) :
    let I' := Binary32.ofBits (w32 ((Vehicle_lib.AC_PID.update_i this dt limit isc).run s).2.m (this + 132).toNat)
    let I := Binary32.ofBits (w32 s.m (this + 132).toNat)
    let E := Binary32.ofBits (w32 s.m (this + 140).toNat)
    let K := Binary32.ofBits (w32 s.m (this + 4).toNat)
    let M := Binary32.ofBits (w32 s.m (this + 16).toNat)
    I' = if (!Vehicle_lib.is_zero.pure' K && Vehicle_lib.is_positive'float.pure' dt) = true then
        (if (!limit || (Vehicle_lib.is_positive'float.pure' I && Vehicle_lib.is_negative'float.pure' E) ||
            (Vehicle_lib.is_negative'float.pure' I && Vehicle_lib.is_positive'float.pure' E)) = true then
          Id.run (Vehicle_lib.constrain_value_line'float.pure' (I + ((E * K) * isc) * dt) (-M) M (Int32.toUInt32 346))
        else I)
      else Binary32.ofBits 0x00000000 := by
  intro I' I E K M
  have hsp0 : s.sp + 0 = s.sp := by simp
  have hsz0 : (PMem.zeroBlock.copySlice 0 s.m s.sp.toNat 16).size = s.m.size :=
    Corpus.Mem.size_copySlice _ _ _ _ _ h.frame.inside (by rw [Corpus.Mem.zeroBlock_size]; omega)
  have hd : Raw { s with sp := s.sp + 16, m := PMem.zeroBlock.copySlice 0 s.m s.sp.toNat 16 } (s.sp + 0) 4 :=
    ⟨by rw [hsp0]; exact h.fp, by rw [hsp0]; simp only [hsz0]; have := h.frame.inside; omega,
     by rw [hsp0]; have := h.frame.nowrap; omega⟩
  have hs : Raw { s with sp := s.sp + 16, m := PMem.zeroBlock.copySlice 0 s.m s.sp.toNat 16 } (this + 4) 4 :=
    ⟨h.ki.bridge, by simp only [hsz0]; exact h.ki.inside, h.ki.nowrap⟩
  have hdisj : (s.sp + 0).toNat + 4 ≤ (this + 4).toNat ∨ (this + 4).toNat + 4 ≤ (s.sp + 0).toNat := by
    rw [hsp0, h.toNat4]; have := h.disj; omega
  have hsz := frameMem_size h
  have hin := h.integ.inside
  have h132 : (this + 132).toNat + 4 ≤ s.sp.toNat ∨ s.sp.toNat + 16 ≤ (this + 132).toNat := by
    rw [h.toNat132]; have := h.disj; omega
  have h16 : (this + 16).toNat + 4 ≤ s.sp.toNat ∨ s.sp.toNat + 16 ≤ (this + 16).toNat := by
    rw [h.toNat16]; have := h.disj; omega
  have h140 : (this + 140).toNat + 4 ≤ s.sp.toNat ∨ s.sp.toNat + 16 ≤ (this + 140).toNat := by
    rw [h.toNat140]; have := h.disj; omega
  have h4 : (this + 4).toNat + 4 ≤ s.sp.toNat ∨ s.sp.toNat + 16 ≤ (this + 4).toNat := by
    rw [h.toNat4]; have := h.disj; omega
  have hd1 : (this + 16).toNat + 4 ≤ (this + 132).toNat ∨ (this + 132).toNat + 4 ≤ (this + 16).toNat := by
    rw [h.toNat16, h.toNat132]; omega
  have eK : w32 (frameMem s.m this s.sp) s.sp.toNat = w32 s.m (this + 4).toNat := by
    unfold frameMem
    have hfr := h.frame.inside
    rw [Corpus.Mem.w32_memcpy4_dst _ _ _ (by rw [hsz0]; omega) (by rw [hsz0]; have := h.ki.inside; omega),
      Corpus.Mem.w32_enter4 _ _ _ (by omega) (by omega)]
  have eI := frameMem_w32 h h132
  have eE := frameMem_w32 h h140
  have eK' := frameMem_w32 h h4
  have eM := frameMem_w32 h h16
  have hI' : I' = Binary32.ofBits (w32 ((Vehicle_lib.AC_PID.update_i this dt limit isc).run s).2.m
      (this + 132).toNat) := rfl
  rw [hI']
  unfold Vehicle_lib.AC_PID.update_i
  rw [StateT.run_bind, Corpus.Mem.enter4_run h.frame]
  simp only [Corpus.id_bind, Corpus.id_run_eq]
  rw [StateT.run_bind]
  unfold Vehicle_lib.AC_PID.update_i.body
  simp only [StateT.run_bind, Corpus.Mem.discard_run, Corpus.Mem.memcpy4_run hd hs hdisj]
  simp only [Corpus.id_bind, Corpus.id_run_eq, StateT.run_bind, hsp0,
    Corpus.AP_Math.is_zero_param_run h.fp, Corpus.AP_Math.is_positive_eq, Corpus.AP_Math.is_negative_eq,
    Corpus.Mem.ldF32_run h.integ.bridge, Corpus.Mem.ldF32_run h.err.bridge, Corpus.Mem.ldF32_run h.ki.bridge,
    Corpus.Mem.ldF32_run h.kimax.bridge, Corpus.Mem.stF32_run h.integ.bridge h.integ.nowrap,
    Corpus.AP_Param.operator_const_float_run, Corpus.AP_Param.operator_neg_run h.kimax.bridge,
    Corpus.AP_Math.constrain_float_eq, StateT.run_pure, Corpus.Mem.leave_run, Corpus.Mem.run_ite,
    Corpus.Mem.discard_run, Corpus.id_pure_eq]
  rw [show ((PMem.zeroBlock.copySlice 0 s.m s.sp.toNat 16).extract (this + 4).toNat
      ((this + 4).toNat + 4)).copySlice 0 (PMem.zeroBlock.copySlice 0 s.m s.sp.toNat 16) s.sp.toNat 4 =
      frameMem s.m this s.sp from rfl]
  simp only [eK, eI, eE, eK']
  have wz : Binary32.ofBits (w32 (set4 (frameMem s.m this s.sp) (this + 132).toNat
      (Binary32.toBits (Binary32.ofBits 0x00000000))) (this + 132).toNat) = Binary32.ofBits 0x00000000 := by
    rw [Corpus.Mem.w32_set4_self _ _ _ (by rw [hsz]; exact hin), Corpus.F32.ofBits_toBits]
  have wu : ∀ x : Binary32, Binary32.ofBits (w32 (updMem (frameMem s.m this s.sp) this x) (this + 132).toNat) =
      Id.run (Vehicle_lib.constrain_value_line'float.pure' x (-M) M (Int32.toUInt32 346)) := by
    intro x
    simp only [updMem]
    rw [Corpus.Mem.w32_set4_self _ _ _ (by rw [Corpus.Mem.size_set4, hsz]; exact hin), Corpus.F32.ofBits_toBits,
      Corpus.Mem.w32_set4_self _ _ _ (by rw [hsz]; exact hin), Corpus.F32.ofBits_toBits,
      Corpus.Mem.w32_set4_of_disjoint _ _ _ _ hd1, eM]
    rfl
  generalize Vehicle_lib.is_zero.pure' K = zk
  generalize Vehicle_lib.is_positive'float.pure' dt = pd
  generalize hPI : Vehicle_lib.is_positive'float.pure' I = pI
  generalize hNE : Vehicle_lib.is_negative'float.pure' E = nE
  generalize hNI : Vehicle_lib.is_negative'float.pure' I = nI
  generalize hPE : Vehicle_lib.is_positive'float.pure' E = pE
  simp only [apply_ite (fun r : Unit × PMem.Mem => Binary32.ofBits (w32 r.2.m (this + 132).toNat))]
  have wf : Binary32.ofBits (w32 (frameMem s.m this s.sp) (this + 132).toNat) = I := by rw [eI]
  simp only [wz, wf]
  rw [show (set4 (set4 (frameMem s.m this s.sp) (this + 132).toNat
      (Binary32.toBits (I + E * K * isc * dt))) (this + 132).toNat _) = updMem (frameMem s.m this s.sp) this
      (I + E * K * isc * dt) from rfl]
  simp only [wu]
  clear hPI hNE hNI hPE
  cases zk <;> cases pd <;> cases limit <;> cases pI <;> cases nE <;> cases nI <;> cases pE <;> rfl
end Corpus.AC_PID

namespace Corpus.AC_PID

/-- Case: with `is_zero(_ki)` or `!is_positive(dt)`, `update_i` zeroes the integrator. -/
theorem update_i_integrator_of_off {s : PMem.Mem} {this : UInt64} (h : Pre s this) (dt : Binary32) (limit : Bool)
    (isc : Binary32)
    (hc : Vehicle_lib.is_zero.pure' (Binary32.ofBits (w32 s.m (this + 4).toNat)) = true ∨
      Vehicle_lib.is_positive'float.pure' dt = false) :
    Binary32.ofBits (w32 ((Vehicle_lib.AC_PID.update_i this dt limit isc).run s).2.m (this + 132).toNat) =
      Binary32.ofBits 0x00000000 := by
  rw [update_i_integrator_cases h dt limit isc]
  rcases hc with hc | hc <;>
    simp only [hc, Bool.not_true, Bool.false_and, Bool.and_false, Bool.false_eq_true, ite_false]

/-- Case: with `!is_zero(_ki)`, `is_positive(dt)`, `limit`, and the integrator and the error not of opposite signs,
`update_i` leaves the integrator unchanged. -/
theorem update_i_integrator_of_hold {s : PMem.Mem} {this : UInt64} (h : Pre s this) (dt : Binary32)
    (isc : Binary32)
    (hk : Vehicle_lib.is_zero.pure' (Binary32.ofBits (w32 s.m (this + 4).toNat)) = false)
    (hdt : Vehicle_lib.is_positive'float.pure' dt = true)
    (hs : ((Vehicle_lib.is_positive'float.pure' (Binary32.ofBits (w32 s.m (this + 132).toNat)) &&
        Vehicle_lib.is_negative'float.pure' (Binary32.ofBits (w32 s.m (this + 140).toNat))) ||
      (Vehicle_lib.is_negative'float.pure' (Binary32.ofBits (w32 s.m (this + 132).toNat)) &&
        Vehicle_lib.is_positive'float.pure' (Binary32.ofBits (w32 s.m (this + 140).toNat)))) = false) :
    Binary32.ofBits (w32 ((Vehicle_lib.AC_PID.update_i this dt true isc).run s).2.m (this + 132).toNat) =
      Binary32.ofBits (w32 s.m (this + 132).toNat) := by
  rw [update_i_integrator_cases h dt true isc]
  simp only [hk, hdt, hs, Bool.not_false, Bool.not_true, Bool.and_self, Bool.false_or, Bool.false_eq_true,
    ite_true, ite_false]

/-- Case: with `!is_zero(_ki)`, `is_positive(dt)`, and `!limit` or the integrator and the error of opposite signs,
`update_i` stores `constrain_float(integrator + ((error * ki) * i_scale) * dt, -kimax, kimax)`. -/
theorem update_i_integrator_of_update {s : PMem.Mem} {this : UInt64} (h : Pre s this) (dt : Binary32) (limit : Bool)
    (isc : Binary32)
    (hk : Vehicle_lib.is_zero.pure' (Binary32.ofBits (w32 s.m (this + 4).toNat)) = false)
    (hdt : Vehicle_lib.is_positive'float.pure' dt = true)
    (hu : (!limit || (Vehicle_lib.is_positive'float.pure' (Binary32.ofBits (w32 s.m (this + 132).toNat)) &&
        Vehicle_lib.is_negative'float.pure' (Binary32.ofBits (w32 s.m (this + 140).toNat))) ||
      (Vehicle_lib.is_negative'float.pure' (Binary32.ofBits (w32 s.m (this + 132).toNat)) &&
        Vehicle_lib.is_positive'float.pure' (Binary32.ofBits (w32 s.m (this + 140).toNat)))) = true) :
    Binary32.ofBits (w32 ((Vehicle_lib.AC_PID.update_i this dt limit isc).run s).2.m (this + 132).toNat) =
      Id.run (Vehicle_lib.constrain_value_line'float.pure'
        (Binary32.ofBits (w32 s.m (this + 132).toNat) + ((Binary32.ofBits (w32 s.m (this + 140).toNat) *
          Binary32.ofBits (w32 s.m (this + 4).toNat)) * isc) * dt)
        (-Binary32.ofBits (w32 s.m (this + 16).toNat)) (Binary32.ofBits (w32 s.m (this + 16).toNat))
        (Int32.toUInt32 346)) := by
  rw [update_i_integrator_cases h dt limit isc]
  simp only [hk, hdt, hu, Bool.not_false, Bool.and_self, ite_true]

end Corpus.AC_PID

/-! ## `update_all`: the non-finite input case, and `UPre` for the controller's PIDs -/

namespace Corpus.AC_PID

open Corpus.Mem (InRegion StackOK)

/-- Case: with a non-finite target or measurement, `update_all` returns `0` at once (the C++ code's first test). -/
theorem update_all_of_not_finite {s : PMem.Mem} {this : UInt64} (h : UPre s this) (target measurement dt : Binary32)
    (limit : Bool) (pd_scale i_scale : Binary32)
    (hc : (!Binary32.isFinite target || !Binary32.isFinite measurement) = true) :
    ((Vehicle_lib.AC_PID.update_all this target measurement dt limit pd_scale i_scale).run s).1 =
      Binary32.ofBits 0x00000000 := by
  have h16 : Raw s s.sp (Corpus.Mem.frameSize 4) := by
    simpa using h.stk.sub (o := 0) (w := 16) (by omega) (by omega)
  unfold Vehicle_lib.AC_PID.update_all
  rw [Corpus.Mem.run_bind', Corpus.Mem.enter_run (by omega) (by decide) h16]
  simp only [Corpus.Mem.run_bind']
  unfold Vehicle_lib.AC_PID.update_all.body
  simp only [hc, ite_true]
  rfl

private theorem sub_obj' {s : PMem.Mem} {a : UInt64} {lo hi n o : Nat} (h : InRegion s a lo hi n)
    (ho : o + 240 ≤ n) : InRegion s (a + o.toUInt64) lo hi 240 := by
  have e := h.toNat_add (o := o) (by omega)
  exact ⟨by rw [e]; have := h.lo_le; omega, by rw [e]; have := h.room; omega, h.inside, h.bridge, h.nowrap⟩

/-- `UPre` for the attitude controller's roll rate PID (the attitude controller in the heap region, 48 bytes of
stack headroom). -/
theorem rate_roll_pid_upre {s : PMem.Mem} {att : UInt64}
    (hst : StackOK s Vehicle_lib.stackBase Vehicle_lib.memSize 48)
    (hatt : InRegion s att Vehicle_lib.heapBase Vehicle_lib.stackBase 1112) :
    UPre s (Id.run (Vehicle_lib.AC_AttitudeControl_Multi.get_rate_roll_pid.pure' att)) :=
  upre_of_regions hst (sub_obj' (o := 376) hatt (by omega))

theorem rate_pitch_pid_upre {s : PMem.Mem} {att : UInt64}
    (hst : StackOK s Vehicle_lib.stackBase Vehicle_lib.memSize 48)
    (hatt : InRegion s att Vehicle_lib.heapBase Vehicle_lib.stackBase 1112) :
    UPre s (Id.run (Vehicle_lib.AC_AttitudeControl_Multi.get_rate_pitch_pid.pure' att)) :=
  upre_of_regions hst (sub_obj' (o := 616) hatt (by omega))

theorem rate_yaw_pid_upre {s : PMem.Mem} {att : UInt64}
    (hst : StackOK s Vehicle_lib.stackBase Vehicle_lib.memSize 48)
    (hatt : InRegion s att Vehicle_lib.heapBase Vehicle_lib.stackBase 1112) :
    UPre s (Id.run (Vehicle_lib.AC_AttitudeControl_Multi.get_rate_yaw_pid.pure' att)) :=
  upre_of_regions hst (sub_obj' (o := 856) hatt (by omega))

theorem accel_pid_upre {s : PMem.Mem} {pos : UInt64}
    (hst : StackOK s Vehicle_lib.stackBase Vehicle_lib.memSize 48)
    (hpos : InRegion s pos Vehicle_lib.heapBase Vehicle_lib.stackBase 984) :
    UPre s (Id.run (Vehicle_lib.AC_PosControl.D_get_accel_pid.pure' pos)) :=
  upre_of_regions hst (sub_obj' (o := 384) hpos (by omega))

end Corpus.AC_PID
