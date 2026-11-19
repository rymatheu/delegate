import ArduLean.Vehicle
import Corpus.Machine.Hoare
import Corpus.Code.AP_Math.AP_Math
import Corpus.Code.Filter.Filter

/-!
# SlewLimiter: `SlewLimiter.cpp` (callee of `AC_PID::update_all`)

C++ `SlewLimiter::modifier : float (float, float)`, `SlewLimiter.cpp:45-138`. The object (78 bytes): `slew_rate_max`
and `slew_rate_tau` are references (pointers at `+0`, `+8`); the slew filter (`LowPassFilter<float>`) at `+16`;
`_output_slew_rate` at `+28`, `_modifier_slew_rate` at `+32`, `last_sample` at `+36`, `_max_pos_slew_rate` at `+40`,
`_max_neg_slew_rate` at `+44`, `_max_pos_slew_event_ms` at `+48`, `_max_neg_slew_event_ms` at `+52`, the window
indices `_pos_event_index`, `_neg_event_index` at `+56`, `+57`, the event windows `_pos_event_ms[2]`,
`_neg_event_ms[2]` at `+60`, `+68`, the flags `_pos_event_stored`, `_neg_event_stored` at `+76`, `+77`.

The Effect proof runs the Hoare-triple steps of `Machine/Hoare.lean` over the body: every store is inside
`[this + 16, this + 78)` or the frames, the window stores through the indices included (the code resets an index
`≥ 2` to `0` just before using it: `Triple.reset_index`).
-/

open FloatLib.Floats (Binary32 Binary64)
open Corpus.Mem (w32 set4 Raw)
open Corpus.Hoare (Agree Ival Inv Triple WOk Stable)
namespace Corpus.Filter

/-- The body's hypotheses on its entry state `s₁`: the slew limiter's 78 bytes and the two 16-byte frames (its own at
`fp`, `LowPassFilter::apply`'s above it) are raw and above the bridged range, disjoint; the stack pointer is past the
own frame. -/
structure ModBody (s₁ : PMem.Mem) (this fp : UInt64) : Prop where
  obj : Raw s₁ this 78
  objHi : PMem.Bridge.hi.toNat ≤ this.toNat
  stk : Raw s₁ fp 32
  stkHi : PMem.Bridge.hi.toNat ≤ fp.toNat
  disj : fp.toNat + 32 ≤ this.toNat ∨ this.toNat + 78 ≤ fp.toNat
  sp : s₁.sp = fp + 16

private theorem ModBody.wok {s₁ : PMem.Mem} {this fp : UInt64} (h : ModBody s₁ this fp) :
    WOk s₁ (fun j => Ival (this.toNat + 16) 62 j ∨ Ival fp.toNat 32 j) := by
  have := h.obj.inside; have := h.stk.inside; have := h.objHi; have := h.stkHi
  have := h.obj.nowrap; have := h.stk.nowrap
  exact ⟨fun j hj => by simp only [Ival] at hj; omega⟩

/-- The call of `LowPassFilter<float>::apply` on the slew filter (`this + 16`), the sample and `dt` in the frame,
keeps the body's invariant. -/
theorem modifier_lpf_call {s₁ : PMem.Mem} {this fp : UInt64} (h : ModBody s₁ this fp) :
    Triple (Inv s₁ (fun j => Ival (this.toNat + 16) 62 j ∨ Ival fp.toNat 32 j) (fun _ => False) (fun _ => True))
      (Vehicle_lib.LowPassFilter'float.apply (this + 16) (fp + 4) (fp + 0))
      (fun _ => Inv s₁ (fun j => Ival (this.toNat + 16) 62 j ∨ Ival fp.toNat 32 j) (fun _ => False) (fun _ => True)) := by
  have ho := h.obj.nowrap; have hf := h.stk.nowrap
  have e16 : (this + 16).toNat = this.toNat + 16 := by rw [UInt64.toNat_add]; simp; omega
  have ef16 : (fp + 16).toNat = fp.toNat + 16 := by rw [UInt64.toNat_add]; simp; omega
  have ef4 : (fp + 4).toNat = fp.toNat + 4 := by rw [UInt64.toNat_add]; simp; omega
  have ef0 : fp + 0 = fp := by simp
  refine Corpus.Hoare.Triple.call (Corpus.Hoare.stable_true _)
    (X := fun j => Ival (this.toNat + 16) 5 j ∨ Ival (fp.toNat + 16) 16 j) (fun s hs => ?_) ?_
  · have hsz := hs.agree.size
    have hsp : s.sp = fp + 16 := by rw [hs.agree.sp, h.sp]
    have pre : LPFApplyPre s (this + 16) (fp + 4) (fp + 0) := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hsp]; exact (h.stk.sub (o := 16) (w := 16) (by omega) (by omega)).congr hsz
      · exact (h.obj.sub (o := 16) (w := 12) (by omega) (by omega)).congr hsz
      · exact (h.stk.sub (o := 4) (w := 4) (by omega) (by omega)).congr hsz
      · rw [ef0]; exact (by simpa using h.stk.sub (o := 0) (w := 4) (by omega) (by omega) : Raw s₁ fp 4).congr hsz
      · rw [hsp]; simp only [ef16, e16]; have := h.disj; omega
      · rw [hsp]; simp only [ef16, ef4]; omega
      · rw [hsp, ef0]; simp only [ef16]; omega
      · simp only [ef4, e16]; have := h.disj; omega
    have := LowPassFilter_apply_agree pre
    rw [hsp, ef16, e16] at this
    exact this
  · intro j hj; simp only [Ival, not_false_eq_true, and_true] at hj ⊢; omega

theorem modifier_body_triple {s₁ : PMem.Mem} {this fp : UInt64} (sample dt : Binary32) (h : ModBody s₁ this fp) :
    Triple (Inv s₁ (fun j => Ival (this.toNat + 16) 62 j ∨ Ival fp.toNat 32 j) (fun _ => False) (fun _ => True))
      (Vehicle_lib.SlewLimiter.modifier.body fp this sample dt)
      (fun _ => Inv s₁ (fun j => Ival (this.toNat + 16) 62 j ∨ Ival fp.toNat 32 j) (fun _ => False) (fun _ => True)) := by
  have hR : Stable (fun _ => True) (fun _ => False) := Corpus.Hoare.stable_true _
  have hW := h.wok
  have ho := h.obj.nowrap
  have hf := h.stk.nowrap
  unfold Vehicle_lib.SlewLimiter.modifier.body
  repeat' triple_step
  all_goals first
    | sub_tac
    | with_reducible exact modifier_lpf_call h
    | with_reducible exact Corpus.Hoare.Triple.of_pure (Corpus.AP_Math.is_positive_eq _)
    | with_reducible exact Corpus.Hoare.Triple.of_state (Corpus.AP_Math.MIN_uint_state _ _)

/-- The hypotheses of `SlewLimiter::modifier`: the slew limiter's 78 bytes raw and above the bridged range; 32 bytes of
stack (its frame and `LowPassFilter::apply`'s) raw, above the bridged range, disjoint from the object. -/
structure ModPre (s : PMem.Mem) (this : UInt64) : Prop where
  obj : Raw s this 78
  objHi : PMem.Bridge.hi.toNat ≤ this.toNat
  stk : Raw s s.sp 32
  stkHi : PMem.Bridge.hi.toNat ≤ s.sp.toNat
  disj : s.sp.toNat + 32 ≤ this.toNat ∨ this.toNat + 78 ≤ s.sp.toNat

/-- Effect: `SlewLimiter::modifier` changes only bytes of the slew limiter from `+16` on (`[this + 16, this + 78)`:
the slew filter, the peak and window fields) and the 32 bytes of stack from the stack pointer (its frame and the
filter's); the stack pointer and every other part of the state are as before. -/
theorem modifier_agree {s : PMem.Mem} {this : UInt64} (h : ModPre s this) (sample dt : Binary32) :
    Agree s ((Vehicle_lib.SlewLimiter.modifier this sample dt).run s).2
      (fun j => Ival (this.toNat + 16) 62 j ∨ Ival s.sp.toNat 32 j) := by
  have h16 : Raw s s.sp (Corpus.Mem.frameSize 12) := by
    simpa using h.stk.sub (o := 0) (w := 16) (by omega) (by omega)
  have hen := Corpus.Mem.enter_run (s := s) (k := 12) (by omega) (by decide) h16
  have hsz := Corpus.Mem.size_enter s.m s.sp.toNat 16 (by have := h.stk.inside; omega) (by omega)
  have hmb : ModBody ((PMem.enter 12).run s).2 this s.sp := by
    rw [hen]
    exact ⟨h.obj.congr hsz, h.objHi, h.stk.congr hsz, h.stkHi, h.disj, rfl⟩
  rw [hen] at hmb
  have hb := modifier_body_triple sample dt hmb _ ⟨Agree.refl _ _, trivial⟩
  unfold Vehicle_lib.SlewLimiter.modifier
  rw [Corpus.Mem.run_bind', hen]
  simp only [Corpus.Mem.run_bind']
  exact Agree.frame hb.agree (by have := h.stk.inside; show s.sp.toNat + 16 ≤ _; omega) (by decide)
    (fun j hj => Or.inr ⟨hj.1, by have := hj.2; unfold Corpus.Mem.frameSize at this; omega⟩)
end Corpus.Filter

namespace Corpus.Filter

/-- Case: with `!is_positive(dt)`, `SlewLimiter::modifier` returns `1` (`SlewLimiter.cpp:47-49`). -/
theorem modifier_of_not_pos {s : PMem.Mem} {this : UInt64} (h : ModPre s this) (sample dt : Binary32)
    (hdt : Vehicle_lib.is_positive'float.pure' dt = false) :
    ((Vehicle_lib.SlewLimiter.modifier this sample dt).run s).1 = Binary32.ofBits 0x3f800000 := by
  have h16 : Raw s s.sp (Corpus.Mem.frameSize 12) := by
    simpa using h.stk.sub (o := 0) (w := 16) (by omega) (by omega)
  have hsz := Corpus.Mem.size_enter s.m s.sp.toNat 16 (by have := h.stk.inside; omega) (by omega)
  have hf4 : Raw s s.sp 4 := by simpa using h.stk.sub (o := 0) (w := 4) (by omega) (by omega)
  have e0 : s.sp + 0 = s.sp := by simp
  unfold Vehicle_lib.SlewLimiter.modifier
  rw [Corpus.Mem.run_bind', Corpus.Mem.enter_run (by omega) (by decide) h16]
  simp only [Corpus.Mem.run_bind']
  unfold Vehicle_lib.SlewLimiter.modifier.body
  simp only [Corpus.Mem.run_bind', e0, Corpus.Mem.stF32_run hf4.bridge hf4.nowrap,
    Corpus.Mem.ldF32_run hf4.bridge]
  have hw : w32 (set4 (PMem.zeroBlock.copySlice 0 s.m s.sp.toNat (Corpus.Mem.frameSize 12)) s.sp.toNat
      (Binary32.toBits dt)) s.sp.toNat = Binary32.toBits dt :=
    Corpus.Mem.w32_set4_self _ _ _ (by
      show s.sp.toNat + 4 ≤ (PMem.zeroBlock.copySlice 0 s.m s.sp.toNat 16).size
      rw [hsz]; have := h.stk.inside; omega)
  have hp : ∀ (x : Binary32) (st : PMem.Mem), StateT.run (Vehicle_lib.is_positive'float x) st =
      (Id.run (Vehicle_lib.is_positive'float.pure' x), st) := fun _ _ => rfl
  simp only [hw, Corpus.F32.ofBits_toBits, hp]
  rw [show Id.run (Vehicle_lib.is_positive'float.pure' dt) = false from hdt]
  exact Corpus.F32.one64_const

end Corpus.Filter

/-! ## `SlewLimiter::modifier`: the value it returns (fourth increment)

The value is a function of `dt`, the target `M` of the `slew_rate_max` reference (the pointer at `+0`, outside the
bytes the call writes) and the field `_modifier_slew_rate` (`+32`) as the call leaves it (`SlewLimiter.cpp:126-137`):
`1` when `!is_positive(dt)` or `M ≤ 0`, else `M / (M + 1.5·(msr - M))` when `msr > M`, else `1`. The proof runs the
value-tracking rules of `Machine/Hoare.lean`: `dt` pinned in the frame, the pointer and its target read through the
agreement with the entry state, the last store to `+32` pinned. -/

namespace Corpus.Filter

/-- The call of `LowPassFilter<float>::apply` keeps an invariant whose pinned bytes `V` are outside the filter's writes. -/
theorem modifier_lpf_pinned_triple {s₁ : PMem.Mem} {this fp : UInt64} (h : ModBody s₁ this fp) {V : Nat → Prop}
    {R : PMem.Mem → Prop} (hR : Stable R V)
    (hV : ∀ j, Ival (this.toNat + 16) 5 j ∨ Ival (fp.toNat + 16) 16 j → ¬ V j) :
    Triple (Inv s₁ (fun j => Ival (this.toNat + 16) 62 j ∨ Ival fp.toNat 32 j) V R)
      (Vehicle_lib.LowPassFilter'float.apply (this + 16) (fp + 4) (fp + 0))
      (fun _ => Inv s₁ (fun j => Ival (this.toNat + 16) 62 j ∨ Ival fp.toNat 32 j) V R) := by
  have ho := h.obj.nowrap; have hf := h.stk.nowrap
  have e16 : (this + 16).toNat = this.toNat + 16 := by rw [UInt64.toNat_add]; simp; omega
  have ef16 : (fp + 16).toNat = fp.toNat + 16 := by rw [UInt64.toNat_add]; simp; omega
  have ef4 : (fp + 4).toNat = fp.toNat + 4 := by rw [UInt64.toNat_add]; simp; omega
  have ef0 : fp + 0 = fp := by simp
  refine Corpus.Hoare.Triple.call hR
    (X := fun j => Ival (this.toNat + 16) 5 j ∨ Ival (fp.toNat + 16) 16 j) (fun s hs => ?_) ?_
  · have hsz := hs.agree.size
    have hsp : s.sp = fp + 16 := by rw [hs.agree.sp, h.sp]
    have pre : LPFApplyPre s (this + 16) (fp + 4) (fp + 0) := by
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · rw [hsp]; exact (h.stk.sub (o := 16) (w := 16) (by omega) (by omega)).congr hsz
      · exact (h.obj.sub (o := 16) (w := 12) (by omega) (by omega)).congr hsz
      · exact (h.stk.sub (o := 4) (w := 4) (by omega) (by omega)).congr hsz
      · rw [ef0]; exact (by simpa using h.stk.sub (o := 0) (w := 4) (by omega) (by omega) : Raw s₁ fp 4).congr hsz
      · rw [hsp]; simp only [ef16, e16]; have := h.disj; omega
      · rw [hsp]; simp only [ef16, ef4]; omega
      · rw [hsp, ef0]; simp only [ef16]; omega
      · simp only [ef4, e16]; have := h.disj; omega
    have := LowPassFilter_apply_agree pre
    rw [hsp, ef16, e16] at this
    exact this
  · intro j hj; refine ⟨?_, hV j hj⟩; simp only [Ival] at hj ⊢; omega

/-- The value `SlewLimiter::modifier` returns, as a function of `dt`, the target `M` of the `slew_rate_max` reference
and the field `_modifier_slew_rate` (`+32`) as the call leaves it. -/
def modVal (dt M msr : Binary32) : Binary32 :=
  if (!Id.run (Vehicle_lib.is_positive'float.pure' dt)) = true then Binary64.toBinary32 (Binary64.ofBits 0x3ff0000000000000)
  else if M ≤ Int32.toBinary32 0 then Binary64.toBinary32 (Binary64.ofBits 0x3ff0000000000000)
  else if msr > M then M / (M + Binary32.ofBits 0x3fc00000 * (msr - M))
  else Binary32.ofBits 0x3f800000

/-- The body's value, from the state after the frame. -/
theorem modifier_body_value {s₁ : PMem.Mem} {this fp p : UInt64} (sample dt : Binary32) (h : ModBody s₁ this fp)
    (hp : (w32 s₁.m this.toNat).toUInt64 ||| ((w32 s₁.m (this + 4).toNat).toUInt64 <<< 32) = p)
    (hpr : Raw s₁ p 4)
    (hpd : p.toNat + 4 ≤ this.toNat + 16 ∨ this.toNat + 78 ≤ p.toNat)
    (hpf : p.toNat + 4 ≤ fp.toNat ∨ fp.toNat + 32 ≤ p.toNat) :
    Triple (Inv s₁ (fun j => Ival (this.toNat + 16) 62 j ∨ Ival fp.toNat 32 j) (fun _ => False) (fun _ => True))
      (Vehicle_lib.SlewLimiter.modifier.body fp this sample dt)
      (fun r s => r = modVal dt (Binary32.ofBits (w32 s₁.m p.toNat)) (Binary32.ofBits (w32 s.m (this + 32).toNat))) := by
  have hR : Stable (fun _ => True) (fun _ => False) := Corpus.Hoare.stable_true _
  have hW := h.wok
  have ho := h.obj.nowrap
  have hf := h.stk.nowrap
  have hd := h.disj
  have hb0 : PMem.inBridgeN this 4 = false := (by simpa using h.obj.sub (o := 0) (w := 4) (by omega) (by omega) : Raw s₁ this 4).bridge
  have hb4 : PMem.inBridgeN (this + 4) 4 = false := (h.obj.sub (o := 4) (w := 4) (by omega) (by omega)).bridge
  have hb32 : PMem.inBridgeN (this + 32) 4 = false := (h.obj.sub (o := 32) (w := 4) (by omega) (by omega)).bridge
  have hbf : PMem.inBridgeN (fp + 0) 4 = false := by
    simpa using (h.stk.sub (o := 0) (w := 4) (by omega) (by omega)).bridge
  have hpv : ∀ {V : Nat → Prop} {R : PMem.Mem → Prop} s,
      Inv s₁ (fun j => Ival (this.toNat + 16) 62 j ∨ Ival fp.toNat 32 j) V R s →
      ((w32 s.m this.toNat).toUInt64 ||| ((w32 s.m (this + 4).toNat).toUInt64 <<< 32)) = p := by
    intro V R s hs
    have e4 : (this + 4).toNat = this.toNat + 4 := by rw [UInt64.toNat_add]; simp; omega
    rw [hs.agree.w32 (a := this.toNat) (fun j h1 h2 => by simp only [Ival]; have := h.disj; omega),
      hs.agree.w32 (a := (this + 4).toNat) (fun j h1 h2 => by rw [e4] at h1 h2; simp only [Ival]; have := h.disj; omega)]
    exact hp
  have hMv : ∀ {V : Nat → Prop} {R : PMem.Mem → Prop} s,
      Inv s₁ (fun j => Ival (this.toNat + 16) 62 j ∨ Ival fp.toNat 32 j) V R s →
      Binary32.ofBits (w32 s.m p.toNat) = Binary32.ofBits (w32 s₁.m p.toNat) := by
    intro V R s hs
    rw [hs.agree.w32 (a := p.toNat) (fun j h1 h2 => by simp only [Ival]; omega)]
  unfold Vehicle_lib.SlewLimiter.modifier.body
  triple_step
  refine Corpus.Hoare.Triple.stF32_pin hR hW (by sub_tac) ?_
  have hR1 := hR.pin32 (fp + 0).toNat (Binary32.toBits dt)
  have hVl : ∀ j, Ival (this.toNat + 16) 5 j ∨ Ival (fp.toNat + 16) 16 j → ¬ (fun j => (fun _ => False) j ∨ Ival (fp + 0).toNat 4 j) j := by
    intro j hj
    simp only [Ival, UInt64.add_zero, false_or, not_and, not_lt] at hj ⊢
    omega
  refine Corpus.Hoare.Triple.ldF32_val hbf (fun s hs => by rw [hs.r.2, Corpus.F32.ofBits_toBits]) ?_
  refine Corpus.Hoare.Triple.pure_val (Corpus.AP_Math.is_positive_eq _) ?_
  refine Corpus.Hoare.Triple.ite (fun hc => ?_) (fun hc => ?_)
  · refine Corpus.Hoare.Triple.pure (fun s _ => ?_)
    exact (ite_cond_eq_true _ _ (eq_true hc)).symm
  · have hpb := hpr.bridge
    repeat' (first
      | with_reducible (refine Corpus.Hoare.Triple.ldU64_val hb0 hb4 hpv ?_)
      | with_reducible (refine Corpus.Hoare.Triple.ldF32_val hpb hMv ?_)
      | with_reducible (refine Corpus.Hoare.Triple.ldF32_val hb32 (fun s hs => by rw [hs.r.2, Corpus.F32.ofBits_toBits]) ?_)
      | (with_reducible refine Corpus.Hoare.Triple.stF32_pin (a := this + 32) (v := Binary32.fmin _ _) (by assumption) hW ?_ ?_
         sub_tac')
      | with_reducible triple_zeta_pure
      | (beta_reduce; guard_triple; with_reducible refine Corpus.Hoare.Triple.pure ?_)
      | triple_step)
    all_goals first
      | sub_tac'
      | with_reducible exact modifier_lpf_pinned_triple h hR1 hVl
      | with_reducible exact Corpus.Hoare.Triple.of_state (Corpus.AP_Math.MIN_uint_state _ _)
      | (intro s hs; exact hs)
      | (intro s hs
         unfold modVal
         try rw [hs.r.2, Corpus.F32.ofBits_toBits]
         simp only [decide_eq_true_eq] at *
         split_ifs <;> first | rfl | contradiction)

/-- Case: the value of `SlewLimiter::modifier`, under the pointer hypotheses: `p` is the `slew_rate_max` reference
(the pointer word at `this`), its 4 bytes raw and outside the bytes the call writes. -/
theorem modifier_eq {s : PMem.Mem} {this p : UInt64} (h : ModPre s this) (sample dt : Binary32)
    (hp : (w32 s.m this.toNat).toUInt64 ||| ((w32 s.m (this + 4).toNat).toUInt64 <<< 32) = p)
    (hpr : Raw s p 4) (hpd : p.toNat + 4 ≤ this.toNat + 16 ∨ this.toNat + 78 ≤ p.toNat)
    (hpf : p.toNat + 4 ≤ s.sp.toNat ∨ s.sp.toNat + 32 ≤ p.toNat) :
    ((Vehicle_lib.SlewLimiter.modifier this sample dt).run s).1 =
      modVal dt (Binary32.ofBits (w32 s.m p.toNat))
        (Binary32.ofBits (w32 ((Vehicle_lib.SlewLimiter.modifier this sample dt).run s).2.m (this + 32).toNat)) := by
  have h16 : Raw s s.sp (Corpus.Mem.frameSize 12) := by
    simpa using h.stk.sub (o := 0) (w := 16) (by omega) (by omega)
  have hen := Corpus.Mem.enter_run (s := s) (k := 12) (by omega) (by decide) h16
  have hsz := Corpus.Mem.size_enter s.m s.sp.toNat 16 (by have := h.stk.inside; omega) (by omega)
  have hin := h.stk.inside
  have hd := h.disj
  have ho := h.obj.nowrap
  have e4 : (this + 4).toNat = this.toNat + 4 := by rw [UInt64.toNat_add]; simp; omega
  have hfs : Corpus.Mem.frameSize 12 = 16 := rfl
  have hmb : ModBody ((PMem.enter 12).run s).2 this s.sp := by
    rw [hen]
    exact ⟨h.obj.congr hsz, h.objHi, h.stk.congr hsz, h.stkHi, h.disj, rfl⟩
  have hp' : (w32 ((PMem.enter 12).run s).2.m this.toNat).toUInt64 |||
      ((w32 ((PMem.enter 12).run s).2.m (this + 4).toNat).toUInt64 <<< 32) = p := by
    rw [hen]; dsimp only; rw [hfs, Corpus.Mem.w32_enter _ _ _ _ (by omega) (by omega) (by omega),
      Corpus.Mem.w32_enter _ _ _ _ (by omega) (by omega) (by rw [e4]; omega)]
    exact hp
  have hpw : w32 ((PMem.enter 12).run s).2.m p.toNat = w32 s.m p.toNat := by
    rw [hen]; dsimp only; rw [hfs, Corpus.Mem.w32_enter _ _ _ _ (by omega) (by omega) (by omega)]
  rw [hen] at hmb hp' hpw
  have hb := modifier_body_value sample dt hmb hp' (hpr.congr hsz) hpd hpf _ ⟨Agree.refl _ _, trivial⟩
  rw [hpw] at hb
  unfold Vehicle_lib.SlewLimiter.modifier
  rw [Corpus.Mem.run_bind', hen]
  simp only [Corpus.Mem.run_bind']
  exact hb


/-- Case: with `is_positive(dt)` and `*slew_rate_max ≤ 0`, the modifier is `1` (`SlewLimiter.cpp:107-109`). -/
theorem modifier_of_nonpos_max {s : PMem.Mem} {this p : UInt64} (h : ModPre s this) (sample dt : Binary32)
    (hp : (w32 s.m this.toNat).toUInt64 ||| ((w32 s.m (this + 4).toNat).toUInt64 <<< 32) = p)
    (hpr : Raw s p 4) (hpd : p.toNat + 4 ≤ this.toNat + 16 ∨ this.toNat + 78 ≤ p.toNat)
    (hpf : p.toNat + 4 ≤ s.sp.toNat ∨ s.sp.toNat + 32 ≤ p.toNat)
    (hdt : Id.run (Vehicle_lib.is_positive'float.pure' dt) = true)
    (hM : Binary32.ofBits (w32 s.m p.toNat) ≤ Binary32.ofBits 0x00000000) :
    ((Vehicle_lib.SlewLimiter.modifier this sample dt).run s).1 = Binary32.ofBits 0x3f800000 := by
  rw [modifier_eq h sample dt hp hpr hpd hpf, modVal, if_neg (by simp [hdt]),
    if_pos (by rw [Corpus.F32.int32_zero]; exact hM), Corpus.F32.one64_const]

/-- Case: with `is_positive(dt)`, `*slew_rate_max > 0` and the modifier slew rate the call leaves at most
`*slew_rate_max`, the modifier is `1`. -/
theorem modifier_of_le {s : PMem.Mem} {this p : UInt64} (h : ModPre s this) (sample dt : Binary32)
    (hp : (w32 s.m this.toNat).toUInt64 ||| ((w32 s.m (this + 4).toNat).toUInt64 <<< 32) = p)
    (hpr : Raw s p 4) (hpd : p.toNat + 4 ≤ this.toNat + 16 ∨ this.toNat + 78 ≤ p.toNat)
    (hpf : p.toNat + 4 ≤ s.sp.toNat ∨ s.sp.toNat + 32 ≤ p.toNat)
    (hdt : Id.run (Vehicle_lib.is_positive'float.pure' dt) = true)
    (hM : ¬ Binary32.ofBits (w32 s.m p.toNat) ≤ Binary32.ofBits 0x00000000)
    (hle : ¬ Binary32.ofBits (w32 ((Vehicle_lib.SlewLimiter.modifier this sample dt).run s).2.m (this + 32).toNat) >
      Binary32.ofBits (w32 s.m p.toNat)) :
    ((Vehicle_lib.SlewLimiter.modifier this sample dt).run s).1 = Binary32.ofBits 0x3f800000 := by
  rw [modifier_eq h sample dt hp hpr hpd hpf, modVal, if_neg (by simp [hdt]),
    if_neg (by rw [Corpus.F32.int32_zero]; exact hM), if_neg hle]

/-- Case: with `is_positive(dt)`, `M = *slew_rate_max > 0` and the modifier slew rate `msr` the call leaves above `M`,
the modifier is `M / (M + 1.5·(msr - M))` (`SlewLimiter.cpp:133-136`). -/
theorem modifier_of_gt {s : PMem.Mem} {this p : UInt64} (h : ModPre s this) (sample dt : Binary32)
    (hp : (w32 s.m this.toNat).toUInt64 ||| ((w32 s.m (this + 4).toNat).toUInt64 <<< 32) = p)
    (hpr : Raw s p 4) (hpd : p.toNat + 4 ≤ this.toNat + 16 ∨ this.toNat + 78 ≤ p.toNat)
    (hpf : p.toNat + 4 ≤ s.sp.toNat ∨ s.sp.toNat + 32 ≤ p.toNat)
    (hdt : Id.run (Vehicle_lib.is_positive'float.pure' dt) = true)
    (hM : ¬ Binary32.ofBits (w32 s.m p.toNat) ≤ Binary32.ofBits 0x00000000)
    (hgt : Binary32.ofBits (w32 ((Vehicle_lib.SlewLimiter.modifier this sample dt).run s).2.m (this + 32).toNat) >
      Binary32.ofBits (w32 s.m p.toNat)) :
    ((Vehicle_lib.SlewLimiter.modifier this sample dt).run s).1 =
      Binary32.ofBits (w32 s.m p.toNat) / (Binary32.ofBits (w32 s.m p.toNat) + Binary32.ofBits 0x3fc00000 *
        (Binary32.ofBits (w32 ((Vehicle_lib.SlewLimiter.modifier this sample dt).run s).2.m (this + 32).toNat) -
          Binary32.ofBits (w32 s.m p.toNat))) := by
  rw [modifier_eq h sample dt hp hpr hpd hpf, modVal, if_neg (by simp [hdt]),
    if_neg (by rw [Corpus.F32.int32_zero]; exact hM), if_pos hgt]

end Corpus.Filter
