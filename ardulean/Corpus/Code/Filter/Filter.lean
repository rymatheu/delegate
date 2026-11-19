import ArduLean.Vehicle
import Corpus.Machine.Float
import Corpus.Machine.Memory
import Corpus.Machine.Hoare
import Corpus.Code.AP_Math.AP_Math

/-!
# Filter: `LowPassFilter.cpp`, `SlewLimiter.cpp`, `AP_Common.h` (callees of `AC_PID::update_all`)

`DigitalLPF<float>::_apply`, `SlewLimiter::get_slew_rate` and (third increment) `LowPassFilter<float>::apply`.
`SlewLimiter::modifier` is in `SlewLimiter.lean`.
-/

open FloatLib.Floats (Binary32 Binary64)
open Corpus.Mem (w32 set4 Raw)

namespace Corpus.Filter

/-- C++ `SlewLimiter::get_slew_rate : float () const`, `AP_Common.h:28-30`: the field at `+28`; the memory
unchanged. -/
theorem get_slew_rate_run {this : UInt64} (hb : PMem.inBridgeN (this + 28) 4 = false) (s : PMem.Mem) :
    (Vehicle_lib.SlewLimiter.get_slew_rate this).run s = (Binary32.ofBits (w32 s.m (this + 28).toNat), s) := by
  unfold Vehicle_lib.SlewLimiter.get_slew_rate
  exact Corpus.Mem.ldF32_run hb

/-- The hypotheses for `DigitalLPF<float>::_apply`: the filter's value (`this`, 4 bytes) raw, its `initialised` flag
(`this + 4`) raw and inside the memory, the sample and the coefficient (4 bytes each) raw and disjoint from the
filter's 5 bytes. -/
structure LPFPre (s : PMem.Mem) (this sample alpha : UInt64) : Prop where
  val : Raw s this 4
  flag : PMem.inBridge (this + 4) = false
  inside : this.toNat + 5 ≤ s.m.size
  smp : Raw s sample 4
  alp : Raw s alpha 4
  disj_smp : sample.toNat + 4 ≤ this.toNat ∨ this.toNat + 5 ≤ sample.toNat
  disj_alp : alpha.toNat + 4 ≤ this.toNat ∨ this.toNat + 5 ≤ alpha.toNat
  nowrap : this.toNat + 5 < 2 ^ 64

/-- The filter's next output: `output + (sample - output) * alpha`, the three read from `m`. -/
abbrev lpfNext (m : ByteArray) (this sample alpha : UInt64) : Binary32 :=
  Binary32.ofBits (w32 m this.toNat) +
    (Binary32.ofBits (w32 m sample.toNat) - Binary32.ofBits (w32 m this.toNat)) * Binary32.ofBits (w32 m alpha.toNat)

/-- C++ `DigitalLPF<float>::_apply : float (const float &, const float &)`, `LowPassFilter.cpp:24-31`. Case: the
result is `output + (sample - output) * alpha` once the filter is initialised (flag byte `≠ 0`), and the sample
itself on the first call. Effect: the output is stored at `this` (and the flag set on the first call); no other byte
and no other part of the state changes. -/
theorem DigitalLPF_apply_run {s : PMem.Mem} {this sample alpha : UInt64} (h : LPFPre s this sample alpha) :
    (Vehicle_lib.DigitalLPF'float._apply this sample alpha).run s =
      if s.m.get! (this.toNat + 4) != 0 then
        (lpfNext s.m this sample alpha,
          { s with m := set4 s.m this.toNat (Binary32.toBits (lpfNext s.m this sample alpha)) })
      else
        (Binary32.ofBits (w32 s.m sample.toNat),
          { s with m := set4 ((set4 s.m this.toNat (Binary32.toBits (lpfNext s.m this sample alpha))).set!
            (this.toNat + 4) 1) this.toNat (Binary32.toBits (Binary32.ofBits (w32 s.m sample.toNat))) }) := by
  have e4 : (this + 4).toNat = this.toNat + 4 := by have := h.nowrap; rw [UInt64.toNat_add]; simp; omega
  have hn4 : this.toNat + 4 < 2 ^ 64 := by have := h.nowrap; omega
  unfold lpfNext
  generalize hv : w32 s.m this.toNat = V
  generalize hsm : w32 s.m sample.toNat = S
  generalize hal : w32 s.m alpha.toNat = A
  unfold Vehicle_lib.DigitalLPF'float._apply
  simp only [StateT.run_bind, Corpus.Mem.ldF32_run h.val.bridge, Corpus.Mem.ldF32_run h.smp.bridge,
    Corpus.Mem.ldF32_run h.alp.bridge, Corpus.id_bind, Corpus.id_run_eq, Corpus.Mem.stF32_run h.val.bridge hn4,
    Corpus.Mem.ldB_run h.flag, hv, hsm, hal, e4]
  have hsz : s.m.size ≥ this.toNat + 4 := by have := h.inside; omega
  rw [Corpus.Mem.get!_set4_of_lt _ _ _ _ (by omega)]
  by_cases hf : (s.m.get! (this.toNat + 4) != 0) = true
  · rw [Corpus.ite_pos hf]
    simp only [hf, Bool.not_true, Bool.false_eq_true, ite_false, StateT.run_bind, Corpus.id_bind, Corpus.id_run_eq,
      Corpus.Mem.ldF32_run h.val.bridge]
    rw [Corpus.Mem.w32_set4_self _ _ _ hsz, Corpus.F32.ofBits_toBits]
  · rw [Corpus.ite_neg hf]
    have hf' : (s.m.get! (this.toNat + 4) != 0) = false := by simpa using hf
    simp only [hf', Bool.not_false, ite_true, StateT.run_bind, Corpus.id_bind, Corpus.id_run_eq,
      Corpus.Mem.stB_run h.flag, e4, Corpus.Mem.ldF32_run h.smp.bridge, Corpus.Mem.stF32_run h.val.bridge hn4,
      Corpus.Mem.ldF32_run h.val.bridge]
    have d1 := h.disj_smp
    rw [Corpus.Mem.w32_set!_of_disjoint _ (this.toNat + 4) sample.toNat _ (by omega),
      Corpus.Mem.w32_set4_of_disjoint _ this.toNat sample.toNat _ (by omega), hsm,
      Corpus.Mem.w32_set4_self _ _ _ (by rw [Corpus.Mem.size_set!, Corpus.Mem.size_set4]; exact hsz),
      Corpus.F32.ofBits_toBits]

end Corpus.Filter

/-! ## `LowPassFilter<float>::apply` (third increment) -/

open Corpus.Hoare (Agree Ival)

namespace Corpus.Filter

/-- The coefficient `calc_lowpass_alpha_dt(dt, cutoff)` (the function reads and writes no memory). -/
def lpAlpha (dt c : Binary32) : Binary32 := ((Vehicle_lib.calc_lowpass_alpha_dt dt c).run default).1

theorem calc_lowpass_alpha_dt_run' (dt c : Binary32) (s : PMem.Mem) :
    (Vehicle_lib.calc_lowpass_alpha_dt dt c).run s = (lpAlpha dt c, s) := by
  unfold lpAlpha; rw [Corpus.AP_Math.calc_lowpass_alpha_dt_run, Corpus.AP_Math.calc_lowpass_alpha_dt_run]

/-- The hypotheses for `LowPassFilter<float>::apply`: its 16-byte frame at the stack pointer, the filter's 12 bytes
(output at `+0`, `initialised` at `+4`, cutoff frequency at `+8`), the sample and `dt` (references, 4 bytes each) are
raw; the frame is disjoint from the other three, and the sample from the filter's output and flag. -/
structure LPFApplyPre (s : PMem.Mem) (this sample dt : UInt64) : Prop where
  frame : Raw s s.sp 16
  obj : Raw s this 12
  smp : Raw s sample 4
  dtr : Raw s dt 4
  fr_obj : s.sp.toNat + 16 ≤ this.toNat ∨ this.toNat + 12 ≤ s.sp.toNat
  fr_smp : s.sp.toNat + 16 ≤ sample.toNat ∨ sample.toNat + 4 ≤ s.sp.toNat
  fr_dt : s.sp.toNat + 16 ≤ dt.toNat ∨ dt.toNat + 4 ≤ s.sp.toNat
  smp_obj : sample.toNat + 4 ≤ this.toNat ∨ this.toNat + 5 ≤ sample.toNat

/-- The memory `LowPassFilter<float>::apply` hands to `DigitalLPF::_apply`: its frame zeroed and the coefficient
stored at the frame's start. -/
abbrev lpfMem (m : ByteArray) (sp : UInt64) (α : Binary32) : ByteArray :=
  set4 (PMem.zeroBlock.copySlice 0 m sp.toNat 16) sp.toNat (Binary32.toBits α)

/-- C++ `LowPassFilter<float>::apply : float (const float &, const float &)`, `LowPassFilter.cpp:119-122`: the frame,
the coefficient from `*dt` and the cutoff at `+8`, then `DigitalLPF<float>::_apply` with the coefficient in the frame;
the stack pointer restored. -/
theorem LowPassFilter_apply_run {s : PMem.Mem} {this sample dt : UInt64} (h : LPFApplyPre s this sample dt) :
    (Vehicle_lib.LowPassFilter'float.apply this sample dt).run s =
      let α := lpAlpha (Binary32.ofBits (w32 s.m dt.toNat)) (Binary32.ofBits (w32 s.m (this + 8).toNat))
      let r := (Vehicle_lib.DigitalLPF'float._apply this sample s.sp).run
        { s with sp := s.sp + 16, m := lpfMem s.m s.sp α }
      (r.1, { r.2 with sp := s.sp }) := by
  have hen := Corpus.Mem.enter_run (s := s) (k := 4) (by omega) (by decide) h.frame
  have hsz : (PMem.zeroBlock.copySlice 0 s.m s.sp.toNat 16).size = s.m.size :=
    Corpus.Mem.size_enter _ _ _ h.frame.inside (by omega)
  have h8 : Raw s (this + 8) 4 := h.obj.sub (o := 8) (w := 4) (by omega) (by omega)
  have e8 : (this + 8).toNat = this.toNat + 8 := by
    have := h.obj.nowrap; rw [UInt64.toNat_add]; simp; omega
  have hf4 : Raw s s.sp 4 := by simpa using h.frame.sub (o := 0) (w := 4) (by omega) (by omega)
  unfold Vehicle_lib.LowPassFilter'float.apply
  rw [Corpus.Mem.run_bind', hen]
  simp only [Corpus.Mem.run_bind']
  unfold Vehicle_lib.LowPassFilter'float.apply.body
  simp only [Corpus.Mem.run_bind', Corpus.Mem.ldF32_run h.dtr.bridge, Corpus.Mem.ldF32_run h8.bridge,
    calc_lowpass_alpha_dt_run', show s.sp + 0 = s.sp by simp,
    Corpus.Mem.stF32_run hf4.bridge hf4.nowrap]
  have hfs : Corpus.Mem.frameSize 4 = 16 := rfl
  have hin : s.sp.toNat ≤ s.m.size := by have := h.frame.inside; omega
  simp only [hfs]
  rw [Corpus.Mem.w32_enter s.m s.sp.toNat 16 _ hin (by decide) (by have := h.fr_dt; omega),
    Corpus.Mem.w32_enter s.m s.sp.toNat 16 _ hin (by decide) (by rw [e8]; have := h.fr_obj; omega)]
  rfl

private theorem LPFApplyPre.inner {s : PMem.Mem} {this sample dt : UInt64} (h : LPFApplyPre s this sample dt) (α : Binary32) :
    LPFPre { s with sp := s.sp + 16, m := lpfMem s.m s.sp α } this sample s.sp := by
  have hsz : (lpfMem s.m s.sp α).size = s.m.size := by
    rw [Corpus.Mem.size_set4, Corpus.Mem.size_enter _ _ _ h.frame.inside (by omega)]
  have h5 := h.obj.sub (o := 4) (w := 1) (by omega) (by omega)
  refine ⟨(by simpa using h.obj.sub (o := 0) (w := 4) (by omega) (by omega) : Raw s this 4).congr hsz,
    by simpa using h.obj.inBridge (o := 4) (by omega), by show this.toNat + 5 ≤ (lpfMem s.m s.sp α).size; rw [hsz]; have := h.obj.inside; omega,
    h.smp.congr hsz, (by simpa using h.frame.sub (o := 0) (w := 4) (by omega) (by omega) : Raw s s.sp 4).congr hsz,
    h.smp_obj, by have := h.fr_obj; omega, by have := h.obj.nowrap; omega⟩

/-- `lpfMem` changes only the frame. -/
private theorem lpfMem_get! {m : ByteArray} {sp : UInt64} {α : Binary32} (hin : sp.toNat + 16 ≤ m.size) {j : Nat}
    (hj : j < sp.toNat ∨ sp.toNat + 16 ≤ j) : (lpfMem m sp α).get! j = m.get! j := by
  rw [Corpus.Mem.get!_set4_of_lt _ _ _ _ (by omega), Corpus.Mem.get!_enter _ _ _ _ (by omega) (by omega) hj]

private theorem lpfMem_w32 {m : ByteArray} {sp : UInt64} {α : Binary32} (hin : sp.toNat + 16 ≤ m.size) {a : Nat}
    (ha : a + 4 ≤ sp.toNat ∨ sp.toNat + 16 ≤ a) : w32 (lpfMem m sp α) a = w32 m a := by
  unfold w32
  rw [lpfMem_get! hin (by omega), lpfMem_get! hin (by omega), lpfMem_get! hin (by omega), lpfMem_get! hin (by omega)]

/-- Case: `LowPassFilter<float>::apply` returns `output + (sample - output) * α` once the filter is initialised (flag
byte at `+4` not zero), and the sample on the first call; `α = calc_lowpass_alpha_dt(*dt, cutoff)`, every value read
before the call. -/
theorem LowPassFilter_apply_eq {s : PMem.Mem} {this sample dt : UInt64} (h : LPFApplyPre s this sample dt) :
    ((Vehicle_lib.LowPassFilter'float.apply this sample dt).run s).1 =
      if s.m.get! (this.toNat + 4) != 0 then
        Binary32.ofBits (w32 s.m this.toNat) +
          (Binary32.ofBits (w32 s.m sample.toNat) - Binary32.ofBits (w32 s.m this.toNat)) *
            lpAlpha (Binary32.ofBits (w32 s.m dt.toNat)) (Binary32.ofBits (w32 s.m (this + 8).toNat))
      else Binary32.ofBits (w32 s.m sample.toNat) := by
  rw [LowPassFilter_apply_run h]
  simp only
  rw [DigitalLPF_apply_run (h.inner _)]
  have hin := h.frame.inside
  have e4 : (lpfMem s.m s.sp (lpAlpha (Binary32.ofBits (w32 s.m dt.toNat))
      (Binary32.ofBits (w32 s.m (this + 8).toNat)))).get! (this.toNat + 4) = s.m.get! (this.toNat + 4) :=
    lpfMem_get! hin (by have := h.fr_obj; omega)
  simp only [e4]
  split
  · simp only [lpfNext]
    rw [lpfMem_w32 hin (by have := h.fr_obj; omega), lpfMem_w32 hin (by have := h.fr_smp; omega),
      Corpus.Mem.w32_set4_self _ _ _ (by rw [Corpus.Mem.size_enter _ _ _ hin (by omega)]; omega),
      Corpus.F32.ofBits_toBits]
  · rw [lpfMem_w32 hin (by have := h.fr_smp; omega)]

/-- Effect: `LowPassFilter<float>::apply` changes only the filter's output and flag (`[this, this + 5)`) and its
frame (`[sp, sp + 16)`); the stack pointer and every other part of the state are as before. -/
theorem LowPassFilter_apply_agree {s : PMem.Mem} {this sample dt : UInt64} (h : LPFApplyPre s this sample dt) :
    Agree s ((Vehicle_lib.LowPassFilter'float.apply this sample dt).run s).2
      (fun j => Ival this.toNat 5 j ∨ Ival s.sp.toNat 16 j) := by
  rw [LowPassFilter_apply_run h]
  simp only
  rw [DigitalLPF_apply_run (h.inner _)]
  have hin := h.frame.inside
  have hsz0 := Corpus.Mem.size_enter _ _ _ hin (show 16 ≤ 4096 by omega)
  have hob := h.obj.inside
  split
  · refine ⟨?_, fun j hj => ?_, rfl⟩
    · simp only [Corpus.Mem.size_set4, hsz0]
    · simp only [Ival, not_or, not_and_or, not_lt, not_le] at hj
      simp only
      rw [Corpus.Mem.get!_set4_of_lt _ _ _ _ (by omega), lpfMem_get! hin (by omega)]
  · refine ⟨?_, fun j hj => ?_, rfl⟩
    · simp only [Corpus.Mem.size_set4, Corpus.Mem.size_set!, hsz0]
    · simp only [Ival, not_or, not_and_or, not_lt, not_le] at hj
      simp only
      rw [Corpus.Mem.get!_set4_of_lt _ _ _ _ (by omega), Corpus.Mem.get!_set!_ne _ _ _ _ (by omega),
        Corpus.Mem.get!_set4_of_lt _ _ _ _ (by omega), lpfMem_get! hin (by omega)]

end Corpus.Filter

namespace Corpus.Filter

/-- `SlewLimiter::get_slew_rate` reads and writes nothing: every precondition is kept. -/
theorem get_slew_rate_triple {P : PMem.Mem → Prop} {this : UInt64} (hb : PMem.inBridgeN (this + 28) 4 = false) :
    Corpus.Hoare.Triple P (Vehicle_lib.SlewLimiter.get_slew_rate this) (fun _ => P) :=
  Corpus.Hoare.Triple.of_state fun s => congrArg Prod.snd (get_slew_rate_run hb s)

end Corpus.Filter

/-! ## `DigitalLPF<T>::get` (`LowPassFilter.cpp`) (fourth increment) -/

namespace Corpus.Filter

/-- C++ `DigitalLPF<float>::get : const float &() const`, `LowPassFilter.cpp:35-37`. -/
theorem DigitalLPF'float.get_eq (this : UInt64) :
    Vehicle_lib.DigitalLPF'float.get this = pure (Vehicle_lib.DigitalLPF'float.get.pure' this) := rfl

/-- Case: the address of the object itself (the value or member is its first field). -/
theorem DigitalLPF'float.get_pure_eq (this : UInt64) : Id.run (Vehicle_lib.DigitalLPF'float.get.pure' this) = this := rfl

/-- C++ `DigitalLPF<Vector3<float>>::get : const Vector3<float> &() const`, `LowPassFilter.cpp:35-37`. -/
theorem DigitalLPF'Vector3_float.get_eq (this : UInt64) :
    Vehicle_lib.DigitalLPF'Vector3_float.get this = pure (Vehicle_lib.DigitalLPF'Vector3_float.get.pure' this) := rfl

/-- Case: the address of the object itself (the value or member is its first field). -/
theorem DigitalLPF'Vector3_float.get_pure_eq (this : UInt64) : Id.run (Vehicle_lib.DigitalLPF'Vector3_float.get.pure' this) = this := rfl

end Corpus.Filter
