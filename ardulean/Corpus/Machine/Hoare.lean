import Corpus.Machine.Memory
import Corpus.Machine.Loop
import ArduLean.Runtime.Boundary

/-!
# Hoare triples over `PMem.M`, and the frame of a run

`Triple P x Q`: from every state satisfying `P`, the run of `x` ends with a result and a state satisfying `Q`.
`Agree s s' W`: `s'` is `s` except for the bytes of `W` (same memory size, every other field equal, the stack pointer
included). A function's Effect lemma is an `Agree` between its entry and exit states.

The rules are syntax-directed on the translation's `do` blocks: `bind`, `pure`, `if`, `discard`, counted loops, and the
`do` elaborator's join points (`have __do_jp := fun … => …; body`), which the tactic `triple_let` treats as a local
procedure with the same pre- and postcondition (the join point is in tail position). The proofs about one code function
run `triple_step` over its body with an invariant of the form `Inv s₁ W V R`: the state agrees with the body's entry
state `s₁` outside `W`, and satisfies `R`, a property that writes outside `V` cannot break. No ArduPilot function
appears here.
-/

open FloatLib.Floats (Binary32 Binary64)

/-! ## Parts of raw ranges -/

namespace Corpus.Mem
theorem inBridgeN_false_iff {a : UInt64} {n : Nat} (hn : a.toNat + n < 2 ^ 64) (hn0 : 0 < n) :
    PMem.inBridgeN a n = false ↔ a.toNat + n ≤ PMem.Bridge.lo.toNat ∨ PMem.Bridge.hi.toNat ≤ a.toNat := by
  have e : (a + n.toUInt64).toNat = a.toNat + n := by
    rw [UInt64.toNat_add, toNat_toUInt64_of_lt (by omega)]; omega
  unfold PMem.inBridgeN
  have : (n != 0) = true := by simp; omega
  rw [this, Bool.true_and]
  simp only [Bool.and_eq_false_iff, decide_eq_false_iff_not, UInt64.lt_iff_toNat_lt, e]
  omega
/-- A part `[a + o, a + o + w)` of a raw range is raw. -/
theorem Raw.sub {s : PMem.Mem} {a : UInt64} {n : Nat} (h : Raw s a n) {o w : Nat} (hw : o + w ≤ n) (hw0 : 0 < w) :
    Raw s (a + o.toUInt64) w := by
  have hn := h.nowrap
  have e : (a + o.toUInt64).toNat = a.toNat + o := by
    rw [UInt64.toNat_add, toNat_toUInt64_of_lt (by omega)]; omega
  have hb := (inBridgeN_false_iff hn (by omega)).1 h.bridge
  refine ⟨(inBridgeN_false_iff (by rw [e]; omega) hw0).2 (by rw [e]; omega), by rw [e]; have := h.inside; omega,
    by rw [e]; omega⟩
theorem Raw.inBridge {s : PMem.Mem} {a : UInt64} {n : Nat} (h : Raw s a n) {o : Nat} (ho : o < n) :
    PMem.inBridge (a + o.toUInt64) = false := by
  have r := h.sub (o := o) (w := 1) (by omega) (by omega)
  have hb := (inBridgeN_false_iff r.nowrap (by omega)).1 r.bridge
  unfold PMem.inBridge
  simp only [UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le, Bool.and_eq_false_iff, decide_eq_false_iff_not]
  omega
theorem Raw.congr {s s' : PMem.Mem} {a : UInt64} {n : Nat} (h : Raw s a n) (hm : s'.m.size = s.m.size) : Raw s' a n :=
  ⟨h.bridge, hm ▸ h.inside, h.nowrap⟩
end Corpus.Mem

namespace Corpus.Hoare

open Corpus.Mem

/-- `s'` is `s` except for the bytes in `W`: the same memory size, the same bytes outside `W`, and every other field of
the state (the stack pointer included) equal. -/
structure Agree (s s' : PMem.Mem) (W : Nat → Prop) : Prop where
  size : s'.m.size = s.m.size
  bytes : ∀ j, ¬ W j → s'.m.get! j = s.m.get! j
  rest : { s' with m := s.m } = s

theorem Agree.refl (s : PMem.Mem) (W : Nat → Prop) : Agree s s W := ⟨rfl, fun _ _ => rfl, rfl⟩

theorem Agree.trans {s s' s'' : PMem.Mem} {W : Nat → Prop} (h : Agree s s' W) (h' : Agree s' s'' W)
    : Agree s s'' W :=
  ⟨h'.size.trans h.size, fun j hj => (h'.bytes j hj).trans (h.bytes j hj), by
    have e1 := h.rest; have e2 := h'.rest
    rw [← e1]; rw [← e2]⟩

theorem Agree.mono {s s' : PMem.Mem} {W W' : Nat → Prop} (h : Agree s s' W) (hW : ∀ j, W j → W' j) :
    Agree s s' W' :=
  ⟨h.size, fun j hj => h.bytes j (fun hw => hj (hW j hw)), h.rest⟩

theorem Agree.sp {s s' : PMem.Mem} {W : Nat → Prop} (h : Agree s s' W) : s'.sp = s.sp := by
  have := congrArg PMem.Mem.sp h.rest; exact this

theorem Agree.w32 {s s' : PMem.Mem} {W : Nat → Prop} (h : Agree s s' W) {a : Nat}
    (ha : ∀ j, a ≤ j → j < a + 4 → ¬ W j) : Corpus.Mem.w32 s'.m a = Corpus.Mem.w32 s.m a := by
  unfold Corpus.Mem.w32
  rw [h.bytes a (ha a (le_refl _) (by omega)), h.bytes (a + 1) (ha _ (by omega) (by omega)),
    h.bytes (a + 2) (ha _ (by omega) (by omega)), h.bytes (a + 3) (ha _ (by omega) (by omega))]

/-- The byte interval `[a, a + n)`. -/
def Ival (a n : Nat) (j : Nat) : Prop := a ≤ j ∧ j < a + n

/-- A property of the memory that no write outside the bytes `V` can break (any other field of the state may
change). -/
def Stable (R : PMem.Mem → Prop) (V : Nat → Prop) : Prop :=
  ∀ s s', R s → s'.m.size = s.m.size → (∀ j, V j → s'.m.get! j = s.m.get! j) → R s'

theorem stable_true (V : Nat → Prop) : Stable (fun _ => True) V := fun _ _ _ _ _ => trivial

/-- The body invariant: agreement with the entry state `s₁` outside `W`, and the property `R`. -/
structure Inv (s₁ : PMem.Mem) (W V : Nat → Prop) (R : PMem.Mem → Prop) (s : PMem.Mem) : Prop where
  agree : Agree s₁ s W
  r : R s

/-- A step that writes only bytes of `X`, with `X` inside `W` and outside `V`, keeps the invariant. -/
theorem Inv.step {s₁ s s' : PMem.Mem} {W V X : Nat → Prop} {R : PMem.Mem → Prop} (hR : Stable R V)
    (h : Inv s₁ W V R s) (hs : Agree s s' X) (hX : ∀ j, X j → W j ∧ ¬ V j) : Inv s₁ W V R s' :=
  ⟨h.agree.trans (hs.mono (fun j hj => (hX j hj).1)),
   hR s s' h.r hs.size (fun j hj => hs.bytes j (fun hx => (hX j hx).2 hj))⟩

/-- A call: the callee's frame of `n` bytes at the stack pointer (`enter`, zeroed), its body agreeing with the entered
state outside `W`, and `leave` restoring the stack pointer give a run that agrees with the caller's state outside `W`,
when `W` contains the frame. -/
theorem Agree.frame {s sb : PMem.Mem} {n : Nat} {W : Nat → Prop}
    (hb : Agree { s with sp := s.sp + n.toUInt64, m := PMem.zeroBlock.copySlice 0 s.m s.sp.toNat n } sb W)
    (hn : s.sp.toNat + n ≤ s.m.size) (hn' : n ≤ 4096) (hW : ∀ j, Ival s.sp.toNat n j → W j) :
    Agree s { sb with sp := s.sp } W := by
  refine ⟨?_, fun j hj => ?_, ?_⟩
  · show sb.m.size = s.m.size
    rw [hb.size]; exact size_enter _ _ _ hn hn'
  · show sb.m.get! j = s.m.get! j
    rw [hb.bytes j hj]
    exact get!_enter _ _ _ _ (by omega) hn' (by
      by_contra hc; exact hj (hW j ⟨by omega, by omega⟩))
  · show { ({ sb with m := PMem.zeroBlock.copySlice 0 s.m s.sp.toNat n } : PMem.Mem) with sp := s.sp, m := s.m } = s
    rw [hb.rest]

/-! ## Triples -/

/-- From every state satisfying `P`, the run of `x` ends in a result and a state satisfying `Q`. -/
def Triple {α : Type} (P : PMem.Mem → Prop) (x : PMem.M α) (Q : α → PMem.Mem → Prop) : Prop :=
  ∀ s, P s → Q (x.run s).1 (x.run s).2

theorem Triple.bind {α β : Type} {P : PMem.Mem → Prop} {R : α → PMem.Mem → Prop} {Q : β → PMem.Mem → Prop}
    {x : PMem.M α} {f : α → PMem.M β} (hx : Triple P x R) (hf : ∀ a, Triple (R a) (f a) Q) :
    Triple P (x >>= f) Q := fun s hs => hf _ _ (hx s hs)

/-- `bind` with the same precondition throughout (the invariant form). -/
theorem Triple.bind_inv {α β : Type} {P : PMem.Mem → Prop} {Q : β → PMem.Mem → Prop}
    {x : PMem.M α} {f : α → PMem.M β} (hx : Triple P x (fun _ => P)) (hf : ∀ a, Triple P (f a) Q) :
    Triple P (x >>= f) Q := Triple.bind hx hf

theorem Triple.pure {α : Type} {P : PMem.Mem → Prop} {Q : α → PMem.Mem → Prop} {a : α} (h : ∀ s, P s → Q a s) :
    Triple P (Pure.pure a) Q := h

theorem Triple.ite {α : Type} {P : PMem.Mem → Prop} {Q : α → PMem.Mem → Prop} {c : Prop} [Decidable c]
    {x y : PMem.M α} (h1 : c → Triple P x Q) (h2 : ¬ c → Triple P y Q) : Triple P (if c then x else y) Q := by
  by_cases hc : c
  · rw [if_pos hc]; exact h1 hc
  · rw [if_neg hc]; exact h2 hc

theorem Triple.conseq {α : Type} {P P' : PMem.Mem → Prop} {Q Q' : α → PMem.Mem → Prop} {x : PMem.M α}
    (h : Triple P' x Q') (hp : ∀ s, P s → P' s) (hq : ∀ a s, Q' a s → Q a s) : Triple P x Q :=
  fun s hs => hq _ _ (h s (hp s hs))

theorem Triple.discard {α : Type} {P : PMem.Mem → Prop} {Q : Unit → PMem.Mem → Prop} {x : PMem.M α}
    (h : Triple P x (fun _ => Q ())) : Triple P (discard x) Q := fun s hs => h s hs

/-- A step that leaves the state unchanged keeps every precondition. -/
theorem Triple.of_state {α : Type} {P : PMem.Mem → Prop} {x : PMem.M α} (h : ∀ s, (x.run s).2 = s) :
    Triple P x (fun _ => P) := fun s hs => by simp only [h s]; exact hs

/-- A state-free step (a pure function's memory-side form, `f … = pure (f.pure' …)`) keeps every precondition. -/
theorem Triple.of_pure {α : Type} {P : PMem.Mem → Prop} {x : PMem.M α} {v : α} (h : x = Pure.pure v) :
    Triple P x (fun _ => P) := Triple.of_state (fun s => by rw [h]; rfl)

/-- A join point (or any local function) `v` used by `body`: prove the property `spec` of `v`, then the body for any
function with that property. -/
theorem Triple.jp {α : Type} {γ : Sort _} {P : PMem.Mem → Prop} {Q : α → PMem.Mem → Prop} (body : γ → PMem.M α)
    (v : γ) (spec : γ → Prop) (hv : spec v) (hb : ∀ jp, spec jp → Triple P (body jp) Q) : Triple P (body v) Q :=
  hb v hv

/-- A counted loop whose iterations keep `P` keeps `P`. -/
theorem Triple.forIn_range {β : Type} {P : PMem.Mem → Prop} (a b : Nat) (init : β)
    (f : Nat → β → PMem.M (ForInStep β)) (h : ∀ i c, Triple P (f i c) (fun _ => P)) :
    Triple P (forIn (m := PMem.M) [a:b] init f) (fun _ => P) := fun s hs =>
  Corpus.Loop.forIn_range_inv (fun _ s => P s) (fun _ s => P s) f a b
    (fun i _ _ c s' h' => by
      have := h i c s' h'
      revert this
      rcases (f i c).run s' with ⟨⟨_⟩ | ⟨_⟩, _⟩ <;> exact id)
    (fun _ _ h => h) init s hs

/-! ## Loads keep every precondition; stores keep the invariant -/

theorem Triple.ldF32 {P : PMem.Mem → Prop} (a : UInt64) : Triple P (PMem.ldF32 a) (fun _ => P) :=
  Triple.of_state (ldF32_state a)
theorem Triple.ldU32 {P : PMem.Mem → Prop} (a : UInt64) : Triple P (PMem.ldU32 a) (fun _ => P) :=
  Triple.of_state (ldU32_state a)
theorem Triple.ldU64 {P : PMem.Mem → Prop} (a : UInt64) : Triple P (PMem.ldU64 a) (fun _ => P) :=
  Triple.of_state (ldU64_state a)
theorem Triple.ldU8 {P : PMem.Mem → Prop} (a : UInt64) : Triple P (PMem.ldU8 a) (fun _ => P) :=
  Triple.of_state (ldU8_state a)
theorem Triple.ldI8 {P : PMem.Mem → Prop} (a : UInt64) : Triple P (PMem.ldI8 a) (fun _ => P) :=
  Triple.of_state (ldI8_state a)
theorem Triple.ldB {P : PMem.Mem → Prop} (a : UInt64) : Triple P (PMem.ldB a) (fun _ => P) :=
  Triple.of_state (ldB_state a)
theorem Triple.ldBits {P : PMem.Mem → Prop} (a : UInt64) (o w : Nat) : Triple P (PMem.ldBits a o w) (fun _ => P) :=
  Triple.of_state (ldBits_state a o w)
theorem Triple.clock {P : PMem.Mem → Prop} : Triple P PMem.clock (fun _ => P) :=
  Triple.of_state (fun _ => rfl)

theorem agree_set4 (s : PMem.Mem) (i : Nat) (v : UInt32) :
    Agree s { s with m := set4 s.m i v } (Ival i 4) :=
  ⟨size_set4 _ _ _, fun j hj => get!_set4_of_lt _ _ _ _ (by unfold Ival at hj; omega), rfl⟩

theorem agree_set! (s : PMem.Mem) (i : Nat) (v : UInt8) :
    Agree s { s with m := s.m.set! i v } (Ival i 1) :=
  ⟨size_set! _ _ _, fun j hj => get!_set!_ne _ _ _ _ (by unfold Ival at hj; omega), rfl⟩

/-- The side condition of a store into `[a, a + n)`: inside `W`, outside `V`. -/
abbrev Sub (a n : Nat) (W V : Nat → Prop) : Prop := ∀ j, a ≤ j → j < a + n → W j ∧ ¬ V j

theorem sub_ival {a n : Nat} {W V : Nat → Prop} (h : Sub a n W V) : ∀ j, Ival a n j → W j ∧ ¬ V j :=
  fun j hj => h j hj.1 hj.2

theorem Triple.stU32 {s₁ : PMem.Mem} {W V : Nat → Prop} {R : PMem.Mem → Prop} (hR : Stable R V) {a : UInt64}
    {v : UInt32} (hraw : Raw s₁ a 4) (hW : Sub a.toNat 4 W V) :
    Triple (Inv s₁ W V R) (PMem.stU32 a v) (fun _ => Inv s₁ W V R) := fun s hs => by
  rw [stU32_run hraw.bridge hraw.nowrap]
  exact hs.step hR (agree_set4 s _ _) (sub_ival hW)

theorem Triple.stF32 {s₁ : PMem.Mem} {W V : Nat → Prop} {R : PMem.Mem → Prop} (hR : Stable R V) {a : UInt64}
    {v : Binary32} (hraw : Raw s₁ a 4) (hW : Sub a.toNat 4 W V) :
    Triple (Inv s₁ W V R) (PMem.stF32 a v) (fun _ => Inv s₁ W V R) :=
  Triple.stU32 hR hraw hW

theorem Triple.stU8 {s₁ : PMem.Mem} {W V : Nat → Prop} {R : PMem.Mem → Prop} (hR : Stable R V) {a : UInt64}
    {v : UInt8} (hraw : Raw s₁ a 1) (hW : Sub a.toNat 1 W V) :
    Triple (Inv s₁ W V R) (PMem.stU8 a v) (fun _ => Inv s₁ W V R) := fun s hs => by
  have hb : PMem.inBridge a = false := by
    have := hraw.bridge; have hn := hraw.nowrap; unfold PMem.inBridgeN at this; unfold PMem.inBridge
    simp only [UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le, UInt64.toNat_add] at this ⊢
    rw [Nat.mod_eq_of_lt (by simp; omega)] at this
    simp at this ⊢; omega
  rw [stU8_run hb]
  exact hs.step hR (agree_set! s _ _) (sub_ival hW)

theorem Triple.stB {s₁ : PMem.Mem} {W V : Nat → Prop} {R : PMem.Mem → Prop} (hR : Stable R V) {a : UInt64}
    {v : Bool} (hraw : Raw s₁ a 1) (hW : Sub a.toNat 1 W V) :
    Triple (Inv s₁ W V R) (PMem.stB a v) (fun _ => Inv s₁ W V R) :=
  Triple.stU8 hR hraw hW

end Corpus.Hoare

/-! ## Stores into a region of raw bytes -/

namespace Corpus.Hoare

open Corpus.Mem

/-- The bytes `W` a body may write are raw: at or above the bridged range, inside the memory, below `2^64 - 1`. -/
structure WOk (s₁ : PMem.Mem) (W : Nat → Prop) : Prop where
  bytes : ∀ j, W j → PMem.Bridge.hi.toNat ≤ j ∧ j < s₁.m.size ∧ j + 1 < 2 ^ 64

theorem WOk.raw {s₁ : PMem.Mem} {W V : Nat → Prop} (hW : WOk s₁ W) {a : UInt64} {n : Nat} (hn : 0 < n)
    (h : Sub a.toNat n W V) : Raw s₁ a n := by
  have h0 := hW.bytes _ (h a.toNat (le_refl _) (by omega)).1
  have h1 := hW.bytes _ (h (a.toNat + n - 1) (by omega) (by omega)).1
  exact ⟨inBridgeN_false_of_ge h0.1, by omega, by omega⟩

theorem Triple.stU32' {s₁ : PMem.Mem} {W V : Nat → Prop} {R : PMem.Mem → Prop} (hR : Stable R V) (hW : WOk s₁ W)
    {a : UInt64} {v : UInt32} (h : Sub a.toNat 4 W V) :
    Triple (Inv s₁ W V R) (PMem.stU32 a v) (fun _ => Inv s₁ W V R) :=
  Triple.stU32 hR (hW.raw (by omega) h) h

theorem Triple.stF32' {s₁ : PMem.Mem} {W V : Nat → Prop} {R : PMem.Mem → Prop} (hR : Stable R V) (hW : WOk s₁ W)
    {a : UInt64} {v : Binary32} (h : Sub a.toNat 4 W V) :
    Triple (Inv s₁ W V R) (PMem.stF32 a v) (fun _ => Inv s₁ W V R) :=
  Triple.stU32 hR (hW.raw (by omega) h) h

theorem Triple.stU8' {s₁ : PMem.Mem} {W V : Nat → Prop} {R : PMem.Mem → Prop} (hR : Stable R V) (hW : WOk s₁ W)
    {a : UInt64} {v : UInt8} (h : Sub a.toNat 1 W V) :
    Triple (Inv s₁ W V R) (PMem.stU8 a v) (fun _ => Inv s₁ W V R) :=
  Triple.stU8 hR (hW.raw (by omega) h) h

theorem Triple.stB' {s₁ : PMem.Mem} {W V : Nat → Prop} {R : PMem.Mem → Prop} (hR : Stable R V) (hW : WOk s₁ W)
    {a : UInt64} {v : Bool} (h : Sub a.toNat 1 W V) :
    Triple (Inv s₁ W V R) (PMem.stB a v) (fun _ => Inv s₁ W V R) :=
  Triple.stU8 hR (hW.raw (by omega) h) h

theorem Triple.stBits' {s₁ : PMem.Mem} {W V : Nat → Prop} {R : PMem.Mem → Prop} (hR : Stable R V) (hW : WOk s₁ W)
    {a : UInt64} {o : Nat} {v : UInt64} (ho : o < 8) (h : Sub a.toNat 1 W V) :
    Triple (Inv s₁ W V R) (PMem.stBits a o 1 v) (fun _ => Inv s₁ W V R) := fun s hs => by
  have hraw := hW.raw (by omega) h
  have hb : PMem.inBridge a = false := by
    have := hraw.bridge; have hn := hraw.nowrap; unfold PMem.inBridgeN at this; unfold PMem.inBridge
    simp only [UInt64.lt_iff_toNat_lt, UInt64.le_iff_toNat_le, UInt64.toNat_add] at this ⊢
    rw [Nat.mod_eq_of_lt (by simp; omega)] at this
    simp at this ⊢; omega
  rw [stBits_run hb ho]
  exact hs.step hR (agree_set! s _ _) (sub_ival h)

/-- `memcpy d src n` between two disjoint raw blocks, the destination inside `W` and outside `V`. -/
theorem Triple.memcpy' {s₁ : PMem.Mem} {W V : Nat → Prop} {R : PMem.Mem → Prop} (hR : Stable R V) (hW : WOk s₁ W)
    {d src n : UInt64} (hn : 0 < n.toNat) (h : Sub d.toNat n.toNat W V) (hs : Raw s₁ src n.toNat)
    (hdisj : d.toNat + n.toNat ≤ src.toNat ∨ src.toNat + n.toNat ≤ d.toNat) :
    Triple (Inv s₁ W V R) (PMem.memcpy d src n) (fun _ => Inv s₁ W V R) := fun s hs' => by
  have hd := hW.raw hn h
  have hsz : s.m.size = s₁.m.size := hs'.agree.size
  rw [memcpy_run hn ⟨hd.bridge, by rw [hsz]; exact hd.inside, hd.nowrap⟩
    ⟨hs.bridge, by rw [hsz]; exact hs.inside, hs.nowrap⟩ hdisj]
  refine hs'.step hR ⟨size_memcpy _ _ _ _ (by rw [hsz]; exact hd.inside) (by rw [hsz]; exact hs.inside),
    fun j hj => get!_memcpy _ _ _ _ _ (by rw [hsz]; exact hd.inside) (by rw [hsz]; exact hs.inside)
      (by unfold Ival at hj; omega), rfl⟩ (sub_ival h)

/-- A callee whose run, from any invariant state, agrees with its entry state outside `X`, keeps the invariant when
`X` is inside `W` and outside `V`. -/
theorem Triple.call {α : Type} {s₁ : PMem.Mem} {W V X : Nat → Prop} {R : PMem.Mem → Prop} (hR : Stable R V)
    {x : PMem.M α} (h : ∀ s, Inv s₁ W V R s → Agree s (x.run s).2 X) (hX : ∀ j, X j → W j ∧ ¬ V j) :
    Triple (Inv s₁ W V R) x (fun _ => Inv s₁ W V R) := fun s hs => hs.step hR (h s hs) hX

end Corpus.Hoare

/-! ## Tactics -/

namespace Corpus.Hoare

open Lean Meta Elab Tactic in
/-- On a goal `Triple P e Q` whose program `e` is a `let`/`have`: a value binding is substituted; a binding of a
function (a join point of the `do` elaborator) becomes `Triple.jp` with the property `∀ x…, Triple P (jp x…) Q`. -/
elab "triple_let" : tactic => withMainContext do
  let g ← getMainGoal
  let tgt ← instantiateMVars (← g.getType)
  let tgt := tgt.cleanupAnnotations
  unless tgt.isAppOfArity ``Corpus.Hoare.Triple 4 do throwError "triple_let: not a Triple"
  let args := tgt.getAppArgs
  let α := args[0]!
  let P := args[1]!
  let e := args[2]!.cleanupAnnotations.headBeta
  let Q := args[3]!
  match e with
  | .letE n ty v b _ =>
    let arity ← forallTelescopeReducing ty fun xs _ => pure xs.size
    if arity == 0 then
      let newTgt := mkAppN tgt.getAppFn #[α, P, b.instantiate1 v, Q]
      replaceMainGoal [← g.replaceTargetDefEq newTgt]
    else
      let body := Expr.lam n ty b .default
      let spec ← withLocalDeclD `jp ty fun jp => do
        let s ← forallTelescopeReducing ty fun xs _ => do
          mkForallFVars xs (mkAppN tgt.getAppFn #[α, P, mkAppN jp xs, Q])
        mkLambdaFVars #[jp] s
      let hvType ← instantiateForall (← inferType spec) #[] -- unused
      let _ := hvType
      let hvT := (Expr.app spec v).headBeta
      let hv ← mkFreshExprSyntheticOpaqueMVar hvT (tag := `jp_spec)
      let hbT ← withLocalDeclD `jp ty fun jp => do
        withLocalDeclD `hjp (Expr.app spec jp).headBeta fun hjp => do
          mkForallFVars #[jp, hjp] (mkAppN tgt.getAppFn #[α, P, (Expr.app body jp).headBeta, Q])
      let hb ← mkFreshExprSyntheticOpaqueMVar hbT (tag := `jp_body)
      let pf ← mkAppOptM ``Corpus.Hoare.Triple.jp #[α, ty, P, Q, body, v, spec, hv, hb]
      g.assign pf
      replaceMainGoal [hv.mvarId!, hb.mvarId!]
  | _ => throwError "triple_let: not a let"

end Corpus.Hoare

/-! ## A reset-then-index pattern, and the step tactic -/

namespace Corpus.Hoare

open Corpus.Mem

theorem idx_zero : (((0 : UInt8).toUInt64.toInt64 * 4).toUInt64 : UInt64) = 0 := by decide
theorem idx_one : (((1 : UInt8).toUInt64.toInt64 * 4).toUInt64 : UInt64) = 4 := by decide

/-- The pattern `if (*a >= 2) *a = 0; i = *a; …` (a one-byte index kept below 2 by a reset just before its use): the
continuation runs with `i ∈ {0, 1}`. The byte `a` is inside `W`, outside `V`. -/
theorem Triple.reset_index {α : Type} {s₁ : PMem.Mem} {W V : Nat → Prop} {R : PMem.Mem → Prop}
    {Q : α → PMem.Mem → Prop} (hR : Stable R V) (hW : WOk s₁ W) {a : UInt64} (ha : Sub a.toNat 1 W V)
    {K : UInt8 → PMem.M α} (hK : ∀ t : UInt8, (t = 0 ∨ t = 1) → Triple (Inv s₁ W V R) (K t) Q) :
    Triple (Inv s₁ W V R)
      (PMem.ldU8 a >>= fun t0 =>
        have jp : Unit → PMem.M α := fun _ => PMem.ldU8 a >>= K
        if decide (t0.toUInt32.toInt32 ≥ 2) = true then
          have c := (Int32.toInt8 0).toUInt8
          PMem.stU8 a c >>= fun r => jp r
        else jp ()) Q := by
  intro s hs
  have hraw := hW.raw (by omega) ha
  have hb : PMem.inBridge a = false := by simpa using hraw.inBridge (o := 0) (by omega)
  have hin : a.toNat < s.m.size := by rw [hs.agree.size]; have := hraw.inside; omega
  simp only [run_bind', ldU8_run hb]
  split
  · rw [run_bind', stU8_run hb, run_bind', ldU8_run hb]
    have hs' : Inv s₁ W V R { s with m := s.m.set! a.toNat (Int32.toInt8 0).toUInt8 } :=
      hs.step hR (agree_set! s _ _) (sub_ival ha)
    have e : ({ s with m := s.m.set! a.toNat (Int32.toInt8 0).toUInt8 } : PMem.Mem).m.get! a.toNat = 0 := by
      show (s.m.set! a.toNat _).get! a.toNat = 0
      rw [get!_set! _ _ _ _ hin, if_pos rfl]; decide
    have := hK _ (Or.inl e) _ hs'
    simpa only [e] using this
  · next hc =>
    rw [run_bind', ldU8_run hb]
    refine hK _ ?_ s hs
    have key : ∀ b : UInt8, ¬ (b.toUInt32.toInt32 ≥ 2) → b.toNat < 2 := by decide +kernel
    have : (s.m.get! a.toNat).toNat < 2 := key _ (by simpa only [decide_eq_true_eq] using hc)
    rcases (show (s.m.get! a.toNat).toNat = 0 ∨ (s.m.get! a.toNat).toNat = 1 by omega) with e | e
    · left; exact UInt8.toNat_inj.1 e
    · right; exact UInt8.toNat_inj.1 e

/-- The side condition of a store: the stored bytes, at an address `base + offset`, inside `W` and outside `V`. -/
macro "sub_tac" : tactic => `(tactic| (
  intro j h1 h2
  simp only [UInt64.toNat_add, UInt64.reduceToNat, idx_zero, idx_one] at h1 h2
  simp only [Ival] at *
  try simp only [not_false_eq_true, and_true, not_or, not_and, not_lt]
  omega))

open Lean Meta Elab Tactic in
/-- Closes a goal `Triple P (jp x…) Q` by a hypothesis `∀ x…, Triple P (jp x…) Q` (the property `triple_let` gives a
join point). -/
elab "triple_call_jp" : tactic => withMainContext do
  let g ← getMainGoal
  for d in ← getLCtx do
    if d.isImplementationDetail then continue
    let ok ← forallTelescopeReducing d.type fun _ b => pure (b.cleanupAnnotations.isAppOfArity ``Corpus.Hoare.Triple 4)
    if !ok then continue
    let s ← saveState
    try
      let gs ← g.apply d.toExpr
      if gs.isEmpty then return
      s.restore
    catch _ => s.restore
  throwError "triple_call_jp: no hypothesis applies"

open Lean Elab Tactic in
/-- Fails unless the goal is a `Triple`. -/
elab "guard_triple" : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  unless tgt.cleanupAnnotations.isAppOfArity ``Corpus.Hoare.Triple 4 do throwError "not a Triple"

/-- One step of a body under the invariant `Inv s₁ W V R` (hypotheses `hR : Stable R V`, `hW : WOk s₁ W` in the
context): loads, stores (their side condition left as a goal), binds, branches, join points, counted loops, `pure`,
the calls of a join point. Only a `Triple` goal is touched, and no code function is unfolded (reducible
transparency). -/
macro "triple_step" : tactic => `(tactic| (guard_triple; with_reducible first
  | (triple_let <;> (try intros) <;> (try beta_reduce))
  | exact Corpus.Hoare.Triple.ldF32 _
  | exact Corpus.Hoare.Triple.ldU32 _
  | exact Corpus.Hoare.Triple.ldU64 _
  | exact Corpus.Hoare.Triple.ldU8 _
  | exact Corpus.Hoare.Triple.ldI8 _
  | exact Corpus.Hoare.Triple.ldB _
  | exact Corpus.Hoare.Triple.ldBits _ _ _
  | exact Corpus.Hoare.Triple.clock
  | apply Corpus.Hoare.Triple.stF32' (by assumption) (by assumption)
  | apply Corpus.Hoare.Triple.stU32' (by assumption) (by assumption)
  | apply Corpus.Hoare.Triple.stB' (by assumption) (by assumption)
  | apply Corpus.Hoare.Triple.stU8' (by assumption) (by assumption)
  | (apply Corpus.Hoare.Triple.stBits' (by assumption) (by assumption) (by omega))
  | (refine Corpus.Hoare.Triple.reset_index (by assumption) (by assumption) ?_ (fun _ ht => ?_) <;>
       try (rcases ht with ht | ht <;> subst ht))
  | (apply Corpus.Hoare.Triple.discard)
  | refine Corpus.Hoare.Triple.forIn_range _ _ _ _ (fun _ _ => ?_)
  | refine Corpus.Hoare.Triple.bind_inv ?_ (fun _ => ?_)
  | refine Corpus.Hoare.Triple.ite (fun _ => ?_) (fun _ => ?_)
  | (apply Corpus.Hoare.Triple.pure; intro _ h; exact h)
  | triple_call_jp))

end Corpus.Hoare

/-! ## The heap (`PMem.alloc`) and calls on the stack (third increment) -/

namespace Corpus.Mem

/-- `alloc n` (`0 < n ≤ 4096`, the block raw): the block at the heap pointer, zeroed; the heap pointer moves past it,
rounded up to a multiple of 16. The memory's other bytes, the stack pointer and every other field are unchanged. -/
theorem alloc_run {s : PMem.Mem} {n : Nat} (hn0 : 0 < n) (hn : n ≤ 4096) (h : Raw s s.hp n) :
    (PMem.alloc n).run s =
      (s.hp, { s with hp := s.hp + (frameSize n).toUInt64, m := PMem.zeroBlock.copySlice 0 s.m s.hp.toNat n }) := by
  have hnn : n.toUInt64.toNat = n := toNat_toUInt64_of_lt (by omega)
  have hb : PMem.inBridgeN s.hp n.toUInt64.toNat = false := by rw [hnn]; exact h.bridge
  have hi := h.inside
  simp only [PMem.alloc, PMem.memset, PMem.memsetRaw, StateT.run, bind, StateT.bind, get, getThe,
    MonadStateOf.get, StateT.get, set, StateT.set, modifyGet, MonadStateOf.modifyGet, StateT.modifyGet, pure,
    StateT.pure, discard, Functor.mapConst, StateT.map, Function.comp]
  have hz : (Int32.toUInt32 0).toUInt8 = 0 := by decide
  have hb' : PMem.inBridgeN s.hp n = false := h.bridge
  simp [zeroBlock_size, hi, hz, hnn, hn0, hn, hb', StateT.bind, StateT.pure, StateT.modifyGet]
  rfl

/-- The heap predicate: the heap pointer is in `[heapBase, stackBase]`, the stack region `[stackBase, top)` follows,
inside the memory, above the bridged range, below `2^64`. -/
structure HeapOK (s : PMem.Mem) (heapBase stackBase : Nat) : Prop where
  lo_le : heapBase ≤ s.hp.toNat
  le_hi : s.hp.toNat ≤ stackBase
  inside : stackBase ≤ s.m.size
  bridge : PMem.Bridge.hi.toNat ≤ heapBase
  nowrap : stackBase + 4096 < 2 ^ 64

/-- `alloc n` within the heap region (`hp + frameSize n ≤ stackBase`; `PMem.alloc` does not check this, FINDINGS
F16): the block it returns lies in the heap region (`InRegion … heapBase stackBase n`), the heap predicate holds
again, the heap pointer has moved by `frameSize n`, and no byte outside the block has changed. -/
theorem HeapOK.alloc {s : PMem.Mem} {heapBase stackBase n : Nat} (h : HeapOK s heapBase stackBase) (hn0 : 0 < n)
    (hn : n ≤ 4096) (hroom : s.hp.toNat + frameSize n ≤ stackBase) :
    ((PMem.alloc n).run s).1 = s.hp ∧
      InRegion ((PMem.alloc n).run s).2 ((PMem.alloc n).run s).1 heapBase stackBase n ∧
      HeapOK ((PMem.alloc n).run s).2 heapBase stackBase ∧
      ((PMem.alloc n).run s).2.hp.toNat = s.hp.toNat + frameSize n ∧ ((PMem.alloc n).run s).2.sp = s.sp ∧
      ((PMem.alloc n).run s).2.m.size = s.m.size ∧
      (∀ j, j < s.hp.toNat ∨ s.hp.toNat + n ≤ j → ((PMem.alloc n).run s).2.m.get! j = s.m.get! j) := by
  have hfs : n ≤ frameSize n := by unfold frameSize; omega
  have hraw : Raw s s.hp n := ⟨inBridgeN_false_of_ge (by have := h.bridge; have := h.lo_le; omega),
    by have := h.inside; omega, by have := h.nowrap; omega⟩
  have hsz := size_enter s.m s.hp.toNat n (by have := h.inside; omega) hn
  have ehp : (s.hp + (frameSize n).toUInt64).toNat = s.hp.toNat + frameSize n := by
    rw [UInt64.toNat_add, toNat_toUInt64_of_lt (by unfold frameSize at *; omega)]
    have := h.nowrap; unfold frameSize at *; omega
  rw [alloc_run hn0 hn hraw]
  refine ⟨rfl, ⟨h.lo_le, by show s.hp.toNat + n ≤ stackBase; omega, by show stackBase ≤ _; rw [hsz]; exact h.inside, h.bridge,
    by have := h.nowrap; omega⟩, ⟨by show heapBase ≤ _; rw [ehp]; have := h.lo_le; omega,
    by show _ ≤ stackBase; rw [ehp]; exact hroom, by show stackBase ≤ _; rw [hsz]; exact h.inside, h.bridge, h.nowrap⟩,
    ehp, rfl, hsz, fun j hj => get!_enter _ _ _ _ (by have := h.inside; omega) hn hj⟩

/-- Two successive allocations return disjoint blocks: the second starts at or past the end of the first. -/
theorem HeapOK.alloc_disjoint {s : PMem.Mem} {heapBase stackBase n : Nat} (h : HeapOK s heapBase stackBase)
    (hn0 : 0 < n) (hn : n ≤ 4096) (hroom : s.hp.toNat + frameSize n ≤ stackBase) :
    s.hp.toNat + n ≤ ((PMem.alloc n).run s).2.hp.toNat := by
  have := (h.alloc hn0 hn hroom).2.2.2.1
  rw [this]; unfold frameSize; omega

/-- A call's stack discipline (`let fp ← enter k; … ; leave fp`): with the caller's stack predicate `StackOK s base top
n` and `frameSize k ≤ n`, the callee's body starts with `StackOK … (n - frameSize k)` and its frame at the caller's
stack pointer, and after `leave` (the body keeping the memory's size) the caller's stack predicate holds again. -/
theorem StackOK.call {s : PMem.Mem} {base top n k : Nat} (h : StackOK s base top n) (hk0 : 0 < k)
    (hk : frameSize k ≤ 4096) (hkn : frameSize k ≤ n) {α : Type} (body : UInt64 → PMem.M α)
    (hbody : ∀ s', ((body s.sp).run s').2.m.size = s'.m.size) :
    StackOK ((PMem.enter k).run s).2 base top (n - frameSize k) ∧ ((PMem.enter k).run s).1 = s.sp ∧
      StackOK ((do let fp ← PMem.enter k; let r ← body fp; PMem.leave fp; pure r : PMem.M α).run s).2 base top n := by
  refine ⟨h.enter hk0 hk hkn, by rw [enter_run hk0 hk (h.raw0 hkn)], ?_⟩
  have e := enter_run hk0 hk (h.raw0 hkn)
  simp only [run_bind', e]
  show StackOK ((PMem.leave s.sp).run ((body s.sp).run _).2).2 base top n
  refine StackOK.leave h ?_
  rw [hbody]
  exact size_enter _ _ _ (by have := h.room; have := h.inside; omega) hk

end Corpus.Mem


/-! ## Value-tracking rules (fourth increment)

Loads whose value the precondition determines (`ldF32_val`, `bind_val`, …), stores that pin the word they write
(`stF32_pin`, `memcpy4_pin`), one-bit stores that keep a property (`stBits_keep`), join points with a precondition
chosen by the caller (`triple_jp`, `triple_jp_w32`), returning join points substituted (`triple_zeta_pure`), the
`Stable` side conditions of growing invariants (`stable_tac`, `triple_step'`), and symbolic execution of straight-line
code over the memory alone (`MemIs`). -/

namespace Corpus.Hoare

open Corpus.Mem

/-- A step whose result every state of the precondition determines, and which leaves the state unchanged: the
continuation runs on that value. -/
theorem Triple.bind_val {α β : Type} {P : PMem.Mem → Prop} {Q : β → PMem.Mem → Prop} {x : PMem.M α}
    {f : α → PMem.M β} {c : α} (hx : ∀ s, P s → x.run s = (c, s)) (h : Triple P (f c) Q) :
    Triple P (x >>= f) Q := fun s hs => by
  rw [run_bind', hx s hs]; exact h s hs

theorem Triple.ldF32_val {α : Type} {P : PMem.Mem → Prop} {Q : α → PMem.Mem → Prop} {a : UInt64} {c : Binary32}
    {f : Binary32 → PMem.M α} (hb : PMem.inBridgeN a 4 = false)
    (hc : ∀ s, P s → Binary32.ofBits (w32 s.m a.toNat) = c) (h : Triple P (f c) Q) :
    Triple P (PMem.ldF32 a >>= f) Q :=
  Triple.bind_val (fun s hs => by rw [ldF32_run hb, hc s hs]) h

theorem Triple.ldU32_val {α : Type} {P : PMem.Mem → Prop} {Q : α → PMem.Mem → Prop} {a : UInt64} {c : UInt32}
    {f : UInt32 → PMem.M α} (hb : PMem.inBridgeN a 4 = false)
    (hc : ∀ s, P s → w32 s.m a.toNat = c) (h : Triple P (f c) Q) :
    Triple P (PMem.ldU32 a >>= f) Q :=
  Triple.bind_val (fun s hs => by rw [ldU32_run hb, hc s hs]) h

theorem Triple.ldU64_val {α : Type} {P : PMem.Mem → Prop} {Q : α → PMem.Mem → Prop} {a : UInt64} {c : UInt64}
    {f : UInt64 → PMem.M α} (hb0 : PMem.inBridgeN a 4 = false) (hb4 : PMem.inBridgeN (a + 4) 4 = false)
    (hc : ∀ s, P s → ((w32 s.m a.toNat).toUInt64 ||| ((w32 s.m (a + 4).toNat).toUInt64 <<< 32)) = c)
    (h : Triple P (f c) Q) :
    Triple P (PMem.ldU64 a >>= f) Q :=
  Triple.bind_val (fun s hs => by rw [ldU64_run hb0 hb4, hc s hs]) h

theorem Triple.ldBits_val {α : Type} {P : PMem.Mem → Prop} {Q : α → PMem.Mem → Prop} {a : UInt64} {o : Nat}
    {c : UInt64} {f : UInt64 → PMem.M α} (hb : PMem.inBridge a = false) (ho : o < 8)
    (hc : ∀ s, P s → bitOf (s.m.get! a.toNat) o = c) (h : Triple P (f c) Q) :
    Triple P (PMem.ldBits a o 1 >>= f) Q :=
  Triple.bind_val (fun s hs => by rw [ldBits_run hb ho, hc s hs]) h

/-- A state-free step (`f … = pure (f.pure' …)`): the continuation runs on its value. -/
theorem Triple.pure_val {α β : Type} {P : PMem.Mem → Prop} {Q : β → PMem.Mem → Prop} {x : PMem.M α}
    {f : α → PMem.M β} {c : α} (hx : x = Pure.pure c) (h : Triple P (f c) Q) : Triple P (x >>= f) Q :=
  Triple.bind_val (fun s _ => by rw [hx]; rfl) h

/-- A word pinned to a value: a property of the memory that only writes into `[a, a + 4)` can break. -/
theorem Stable.pin32 {R : PMem.Mem → Prop} {V : Nat → Prop} (hR : Stable R V) (a : Nat) (v : UInt32) :
    Stable (fun s => R s ∧ w32 s.m a = v) (fun j => V j ∨ Ival a 4 j) := by
  intro s s' ⟨hr, hv⟩ hsz hb
  refine ⟨hR s s' hr hsz (fun j hj => hb j (Or.inl hj)), ?_⟩
  rw [← hv]; unfold w32
  rw [hb a (Or.inr ⟨le_refl _, by omega⟩), hb (a + 1) (Or.inr ⟨by omega, by omega⟩),
    hb (a + 2) (Or.inr ⟨by omega, by omega⟩), hb (a + 3) (Or.inr ⟨by omega, by omega⟩)]

/-- A store that pins the word it writes: the continuation runs under the invariant with the word added to the pinned
bytes `V` and its value to `R` (later stores must stay off it). -/
theorem Triple.stF32_pin {α : Type} {s₁ : PMem.Mem} {W V : Nat → Prop} {R : PMem.Mem → Prop}
    {Q : α → PMem.Mem → Prop} (hR : Stable R V) (hW : WOk s₁ W) {a : UInt64} {v : Binary32}
    (hs : Sub a.toNat 4 W V) {K : PUnit → PMem.M α}
    (hK : Triple (Inv s₁ W (fun j => V j ∨ Ival a.toNat 4 j)
      (fun s => R s ∧ w32 s.m a.toNat = Binary32.toBits v)) (K ()) Q) :
    Triple (Inv s₁ W V R) (PMem.stF32 a v >>= K) Q := fun s h => by
  have hraw := hW.raw (by omega) hs
  rw [run_bind', stF32_run hraw.bridge hraw.nowrap]
  have h' := h.step hR (agree_set4 s a.toNat (Binary32.toBits v)) (sub_ival hs)
  exact hK _ ⟨h'.agree, h'.r, w32_set4_self _ _ _ (by rw [h.agree.size]; exact hraw.inside)⟩

end Corpus.Hoare

namespace Corpus.Hoare

/-- A join point with a precondition chosen by the caller: `spec jp` is `∀ xs, Triple (J xs) (jp xs) Q`. -/
theorem Triple.jp_with {α : Type} {γ : Sort _} {P : PMem.Mem → Prop} {Q : α → PMem.Mem → Prop}
    (body : γ → PMem.M α) (v : γ) (spec : γ → Prop) (hv : spec v) (hb : ∀ jp, spec jp → Triple P (body jp) Q) :
    Triple P (body v) Q := hb v hv

open Lean Meta Elab Tactic in
/-- On a goal `Triple P (have jp := v; body) Q` whose `jp` is a function (a join point): the join point gets the
precondition `J xs` chosen by the caller (`J : xs… → PMem.Mem → Prop`). Two goals: `∀ xs, Triple (J xs) (v xs) Q`,
and the body for any `jp` with that property. -/
elab "triple_jp " J:term : tactic => withMainContext do
  let g ← getMainGoal
  let tgt ← instantiateMVars (← g.getType)
  let tgt := tgt.cleanupAnnotations
  unless tgt.isAppOfArity ``Corpus.Hoare.Triple 4 do throwError "triple_jp: not a Triple"
  let args := tgt.getAppArgs
  let α := args[0]!
  let P := args[1]!
  let e := args[2]!.cleanupAnnotations.headBeta
  let Q := args[3]!
  match e with
  | .letE n ty v b _ =>
    let jTy ← forallTelescope ty fun xs _ => do
      mkForallFVars xs (← mkArrow (mkConst ``PMem.Mem) (mkSort Level.zero))
    let Je ← Term.elabTermEnsuringType J jTy
    Term.synthesizeSyntheticMVarsNoPostponing
    let Je ← instantiateMVars Je
    let body := Expr.lam n ty b .default
    let spec ← withLocalDeclD `jp ty fun jp => do
      let s ← forallTelescope ty fun xs _ => do
        mkForallFVars xs (mkAppN tgt.getAppFn #[α, (mkAppN Je xs).headBeta, mkAppN jp xs, Q])
      mkLambdaFVars #[jp] s
    let hvT := (Expr.app spec v).headBeta
    let hv ← mkFreshExprSyntheticOpaqueMVar hvT (tag := `jp_spec)
    let hbT ← withLocalDeclD `jp ty fun jp => do
      withLocalDeclD `hjp (Expr.app spec jp).headBeta fun hjp => do
        mkForallFVars #[jp, hjp] (mkAppN tgt.getAppFn #[α, P, (Expr.app body jp).headBeta, Q])
    let hb ← mkFreshExprSyntheticOpaqueMVar hbT (tag := `jp_body)
    let pf ← mkAppOptM ``Corpus.Hoare.Triple.jp_with #[α, ty, P, Q, body, v, spec, hv, hb]
    g.assign pf
    replaceMainGoal [hv.mvarId!, hb.mvarId!]
  | _ => throwError "triple_jp: not a let"

open Lean Meta Elab Tactic in
/-- On a goal `Triple P (have x := v; body) Q`: substitute `v` for `x`, whatever `v` is (a join point included). -/
elab "triple_zeta" : tactic => withMainContext do
  let g ← getMainGoal
  let tgt ← instantiateMVars (← g.getType)
  let tgt := tgt.cleanupAnnotations
  unless tgt.isAppOfArity ``Corpus.Hoare.Triple 4 do throwError "triple_zeta: not a Triple"
  let args := tgt.getAppArgs
  let e := args[2]!.cleanupAnnotations.headBeta
  match e with
  | .letE _ _ v b _ =>
    replaceMainGoal [← g.replaceTargetDefEq (mkAppN tgt.getAppFn #[args[0]!, args[1]!, b.instantiate1 v, args[3]!])]
  | _ => throwError "triple_zeta: not a let"

open Lean Meta Elab Tactic in
/-- On a goal `Triple P (have jp := fun xs => pure e; body) Q` (a join point that only returns): substitute it, so
that each call returns its own value. -/
elab "triple_zeta_pure" : tactic => withMainContext do
  let g ← getMainGoal
  let tgt ← instantiateMVars (← g.getType)
  let tgt := tgt.cleanupAnnotations
  unless tgt.isAppOfArity ``Corpus.Hoare.Triple 4 do throwError "triple_zeta_pure: not a Triple"
  let args := tgt.getAppArgs
  let e := args[2]!.cleanupAnnotations.headBeta
  match e with
  | .letE _ _ v b _ =>
    let ok ← lambdaTelescope v fun xs bd => pure (xs.size > 0 && bd.cleanupAnnotations.isAppOf ``Pure.pure)
    unless ok do throwError "triple_zeta_pure: not a returning join point"
    replaceMainGoal [← g.replaceTargetDefEq (mkAppN tgt.getAppFn #[args[0]!, args[1]!, b.instantiate1 v, args[3]!])]
  | _ => throwError "triple_zeta_pure: not a let"

/-- The side condition of a store (`Sub`), with the base addresses' offsets (`fp + 0` included) unfolded everywhere. -/
macro "sub_tac'" : tactic => `(tactic| (
  intro j h1 h2
  simp only [UInt64.toNat_add, UInt64.reduceToNat, Corpus.Hoare.idx_zero, Corpus.Hoare.idx_one, UInt64.add_zero,
    Corpus.Hoare.Ival] at *
  try simp (disch := omega) only [Nat.mod_eq_of_lt] at *
  try simp only [not_false_eq_true, and_true, true_and, false_or, or_false, not_or, not_and, not_lt]
  omega))

/-- A call of a join point `jp xs` from a state satisfying `P`, by its property `∀ xs, Triple (J xs) (jp xs) Q`. -/
theorem Triple.of_jp {α : Type} {P P' : PMem.Mem → Prop} {Q : α → PMem.Mem → Prop} {x : PMem.M α}
    (h : Triple P' x Q) (hp : ∀ s, P s → P' s) : Triple P x Q := fun s hs => h s (hp s hs)

end Corpus.Hoare

namespace Corpus.Hoare

open Corpus.Mem

/-- A precondition that is one exact state: a step whose run from that state is known continues from its end state. -/
theorem Triple.bind_exact {α β : Type} {S S' : PMem.Mem} {Q : β → PMem.Mem → Prop} {x : PMem.M α}
    {f : α → PMem.M β} {c : α} (hx : x.run S = (c, S')) (h : Triple (fun s => s = S') (f c) Q) :
    Triple (fun s => s = S) (x >>= f) Q := fun s hs => by
  subst hs; rw [run_bind', hx]; exact h _ rfl

/-- A word that a `memcpy` of 4 bytes pins: the destination's word is the source's, whose value every state of the
precondition determines. -/
theorem Triple.memcpy4_pin {α : Type} {s₁ : PMem.Mem} {W V : Nat → Prop} {R : PMem.Mem → Prop}
    {Q : α → PMem.Mem → Prop} (hR : Stable R V) (hW : WOk s₁ W) {d src : UInt64} {c : UInt32}
    (h : Sub d.toNat 4 W V) (hs : Raw s₁ src 4)
    (hdisj : d.toNat + 4 ≤ src.toNat ∨ src.toNat + 4 ≤ d.toNat)
    (hc : ∀ s, Inv s₁ W V R s → w32 s.m src.toNat = c) {K : PUnit → PMem.M α}
    (hK : Triple (Inv s₁ W (fun j => V j ∨ Ival d.toNat 4 j) (fun s => R s ∧ w32 s.m d.toNat = c)) (K ()) Q) :
    Triple (Inv s₁ W V R) (Functor.discard (PMem.memcpy d src 4) >>= K) Q := fun s hs' => by
  have hd := hW.raw (by omega) h
  have hsz : s.m.size = s₁.m.size := hs'.agree.size
  have e4 : (4 : UInt64).toNat = 4 := rfl
  have hd' : Raw s d (4 : UInt64).toNat := ⟨hd.bridge, by rw [hsz]; exact hd.inside, hd.nowrap⟩
  have hs'' : Raw s src (4 : UInt64).toNat := ⟨hs.bridge, by rw [hsz]; exact hs.inside, hs.nowrap⟩
  rw [run_bind', discard_run, memcpy_run (by decide) hd' hs'' hdisj]
  simp only [e4]
  have hi1 : d.toNat + 4 ≤ s.m.size := by rw [hsz]; exact hd.inside
  have hi2 : src.toNat + 4 ≤ s.m.size := by rw [hsz]; exact hs.inside
  have hag : Agree s { s with m := (s.m.extract src.toNat (src.toNat + 4)).copySlice 0 s.m d.toNat 4 }
      (Ival d.toNat 4) :=
    ⟨size_memcpy _ _ _ _ hi1 hi2, fun j hj => get!_memcpy _ _ _ _ _ hi1 hi2 (by unfold Ival at hj; omega), rfl⟩
  have h' := hs'.step hR hag (sub_ival h)
  refine hK _ ⟨h'.agree, h'.r, ?_⟩
  show w32 ((s.m.extract src.toNat (src.toNat + 4)).copySlice 0 s.m d.toNat 4) d.toNat = c
  have := w32_memcpy_dst s.m d.toNat src.toNat 4 0 hi1 hi2 (by omega)
  simp only [Nat.add_zero] at this
  rw [this, hc s hs']

/-- A one-bit store into a byte inside `W`, for a property `R` that a change of that bit keeps. -/
theorem Triple.stBits_keep {s₁ : PMem.Mem} {W V : Nat → Prop} {R : PMem.Mem → Prop} (hW : WOk s₁ W)
    {a : UInt64} {o : Nat} {v : UInt64} (ho : o < 8) (h : ∀ j, a.toNat ≤ j → j < a.toNat + 1 → W j)
    (hRb : ∀ s, Inv s₁ W V R s →
      R { s with m := s.m.set! a.toNat (setBit (s.m.get! a.toNat) o (v.toNat % 2 = 1)) }) :
    Triple (Inv s₁ W V R) (PMem.stBits a o 1 v) (fun _ => Inv s₁ W V R) := fun s hs => by
  have hraw := hW.raw (V := fun _ => False) (by omega) (fun j h1 h2 => ⟨h j h1 h2, id⟩)
  have hb : PMem.inBridge a = false := by simpa using hraw.inBridge (o := 0) (by omega)
  rw [stBits_run hb ho]
  exact ⟨hs.agree.trans ((agree_set! s _ _).mono (fun j hj => h j hj.1 hj.2)), hRb s hs⟩

/-- A property that does not depend on the state is stable. -/
theorem Stable.and_const {R : PMem.Mem → Prop} {V : Nat → Prop} (hR : Stable R V) (c : Prop) :
    Stable (fun s => R s ∧ c) V := fun s s' h hsz hb => ⟨hR s s' h.1 hsz hb, h.2⟩

/-- A bit of a byte pinned to a value. -/
theorem Stable.pinBit {R : PMem.Mem → Prop} {V : Nat → Prop} (hR : Stable R V) (a o : Nat) (c : UInt64) :
    Stable (fun s => R s ∧ bitOf (s.m.get! a) o = c) (fun j => V j ∨ Ival a 1 j) := by
  intro s s' ⟨hr, hv⟩ hsz hb
  refine ⟨hR s s' hr hsz (fun j hj => hb j (Or.inl hj)), ?_⟩
  rw [hb a (Or.inr ⟨le_refl _, by omega⟩)]; exact hv

/-- `Stable` for a larger set of pinned bytes. -/
theorem Stable.mono {R : PMem.Mem → Prop} {V V' : Nat → Prop} (hR : Stable R V) (hV : ∀ j, V j → V' j) :
    Stable R V' := fun s s' h hsz hb => hR s s' h hsz (fun j hj => hb j (hV j hj))

open Lean Meta Elab Tactic in
/-- Fails on a goal `Triple P (have jp := fun x₁ … xₙ => …; body) Q` whose join point takes at least `n` arguments. -/
elab "guard_not_jp " n:num : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  let tgt := tgt.cleanupAnnotations
  if tgt.isAppOfArity ``Corpus.Hoare.Triple 4 then
    let e := tgt.getAppArgs[2]!.cleanupAnnotations.headBeta
    if let .letE _ ty _ _ _ := e then
      let k ← forallTelescope ty fun xs _ => pure xs.size
      if k ≥ n.getNat then throwError "guard_not_jp: a join point of {k} arguments"

end Corpus.Hoare

namespace Corpus.Hoare

open Corpus.Mem

/-- A conjunct that depends on the state through one pinned word only. -/
theorem Stable.and_w32 {R : PMem.Mem → Prop} {V : Nat → Prop} (hR : Stable R V) (a : Nat) (G : UInt32 → Prop)
    (hV : ∀ j, Ival a 4 j → V j) : Stable (fun s => R s ∧ G (w32 s.m a)) V := by
  intro s s' ⟨hr, hg⟩ hsz hb
  refine ⟨hR s s' hr hsz hb, ?_⟩
  have e : w32 s'.m a = w32 s.m a := by
    unfold w32
    rw [hb a (hV _ ⟨le_refl _, by omega⟩), hb (a + 1) (hV _ ⟨by omega, by omega⟩),
      hb (a + 2) (hV _ ⟨by omega, by omega⟩), hb (a + 3) (hV _ ⟨by omega, by omega⟩)]
  rw [e]; exact hg

/-- `Stable` for the invariants the value-tracking rules build: pinned words, pinned bits, constant conjuncts. -/
syntax "stable_tac" : tactic
macro_rules | `(tactic| stable_tac) => `(tactic| first
  | assumption
  | exact Corpus.Hoare.stable_true _
  | (refine Corpus.Hoare.Stable.pin32 ?_ _ _; stable_tac)
  | (refine Corpus.Hoare.Stable.pinBit ?_ _ _ _; stable_tac)
  | (refine Corpus.Hoare.Stable.and_w32 ?_ _ _ ?_
     · stable_tac
     · intro j hj; simp only [Corpus.Hoare.Ival] at hj ⊢; omega)
  | (refine Corpus.Hoare.Stable.and_const ?_ _; stable_tac))

open Lean Meta Elab Tactic in
/-- On a goal `Triple (Inv s₁ W V R) (have jp := v; body) Q` whose `jp` is a function: the join point gets the
precondition `Inv s₁ W V (fun s => R s ∧ G xs (w32 s.m a))` (`G : xs… → UInt32 → Prop`), a property of its
arguments read through the pinned word at `a`. Two goals, as `triple_jp`. -/
elab "triple_jp_w32 " G:term " at " a:term : tactic => withMainContext do
  let g ← getMainGoal
  let tgt ← instantiateMVars (← g.getType)
  let tgt := tgt.cleanupAnnotations
  unless tgt.isAppOfArity ``Corpus.Hoare.Triple 4 do throwError "triple_jp_w32: not a Triple"
  let args := tgt.getAppArgs
  let P := args[1]!.cleanupAnnotations
  unless P.isAppOfArity ``Corpus.Hoare.Inv 4 do throwError "triple_jp_w32: the precondition is not an Inv"
  let pa := P.getAppArgs
  let e := args[2]!.cleanupAnnotations.headBeta
  match e with
  | .letE _ ty _ _ _ =>
    let gTy ← forallTelescope ty fun xs _ => do
      mkForallFVars xs (← mkArrow (mkConst ``UInt32) (mkSort Level.zero))
    let Ge ← Term.elabTermEnsuringType G gTy
    let ae ← Term.elabTermEnsuringType a (mkConst ``Nat)
    Term.synthesizeSyntheticMVarsNoPostponing
    let Ge ← instantiateMVars Ge
    let ae ← instantiateMVars ae
    let J ← forallTelescope ty fun xs _ => do
      let Rn ← withLocalDeclD `s (mkConst ``PMem.Mem) fun s => do
        let w ← mkAppM ``Corpus.Mem.w32 #[← mkAppM ``PMem.Mem.m #[s], ae]
        mkLambdaFVars #[s] (mkAnd (mkApp pa[3]! s).headBeta (mkApp (mkAppN Ge xs) w).headBeta)
      mkLambdaFVars xs (mkAppN P.getAppFn #[pa[0]!, pa[1]!, pa[2]!, Rn])
    let stx ← `(tactic| triple_jp $(← Term.exprToSyntax J))
    evalTactic stx
  | _ => throwError "triple_jp_w32: not a let"

/-- `triple_step` with the `Stable` side condition of a store found by `stable_tac` (for invariants that grow
by pinning). -/
macro "triple_step'" : tactic => `(tactic| (guard_triple; with_reducible first
  | (triple_let <;> (try intros) <;> (try beta_reduce))
  | exact Corpus.Hoare.Triple.ldF32 _
  | exact Corpus.Hoare.Triple.ldU32 _
  | exact Corpus.Hoare.Triple.ldU64 _
  | exact Corpus.Hoare.Triple.ldU8 _
  | exact Corpus.Hoare.Triple.ldI8 _
  | exact Corpus.Hoare.Triple.ldB _
  | exact Corpus.Hoare.Triple.ldBits _ _ _
  | exact Corpus.Hoare.Triple.clock
  | apply Corpus.Hoare.Triple.stF32' (by stable_tac) (by assumption)
  | apply Corpus.Hoare.Triple.stU32' (by stable_tac) (by assumption)
  | apply Corpus.Hoare.Triple.stB' (by stable_tac) (by assumption)
  | apply Corpus.Hoare.Triple.stU8' (by stable_tac) (by assumption)
  | (apply Corpus.Hoare.Triple.stBits' (by stable_tac) (by assumption) (by omega))
  | (apply Corpus.Hoare.Triple.discard)
  | refine Corpus.Hoare.Triple.forIn_range _ _ _ _ (fun _ _ => ?_)
  | refine Corpus.Hoare.Triple.bind_inv ?_ (fun _ => ?_)
  | refine Corpus.Hoare.Triple.ite (fun _ => ?_) (fun _ => ?_)
  | (apply Corpus.Hoare.Triple.pure; intro _ h; exact h)
  | triple_call_jp))

end Corpus.Hoare

namespace Corpus.Hoare

open Lean Meta Elab Tactic in
/-- Fails unless the goal is `Triple P (f xs…) Q` with `f` a local (a join point's call). -/
elab "guard_jp_call" : tactic => withMainContext do
  let tgt ← instantiateMVars (← getMainTarget)
  let tgt := tgt.cleanupAnnotations
  unless tgt.isAppOfArity ``Corpus.Hoare.Triple 4 do throwError "guard_jp_call: not a Triple"
  let e := tgt.getAppArgs[2]!.cleanupAnnotations.headBeta
  unless e.getAppFn.isFVar do throwError "guard_jp_call: not a call of a local"

end Corpus.Hoare

namespace Corpus.Hoare

open Corpus.Mem

/-- The state is `s₁` except for its memory, which is `M` (symbolic execution of straight-line code over the
memory alone). -/
def MemIs (s₁ : PMem.Mem) (M : ByteArray) (s : PMem.Mem) : Prop := { s with m := s₁.m } = s₁ ∧ s.m = M

theorem MemIs.start (s₁ : PMem.Mem) : ∀ s, s = s₁ → MemIs s₁ s₁.m s := fun s hs => by subst hs; exact ⟨rfl, rfl⟩

/-- A step that keeps the state and whose value the memory `M` determines. -/
theorem Triple.val_mem {α β : Type} {s₁ : PMem.Mem} {M : ByteArray} {Q : β → PMem.Mem → Prop} {x : PMem.M α}
    {f : α → PMem.M β} {c : α} (hx : ∀ s, MemIs s₁ M s → x.run s = (c, s)) (h : Triple (MemIs s₁ M) (f c) Q) :
    Triple (MemIs s₁ M) (x >>= f) Q := Triple.bind_val hx h

theorem Triple.ldF32_mem {α : Type} {s₁ : PMem.Mem} {M : ByteArray} {Q : α → PMem.Mem → Prop} {a : UInt64}
    {f : Binary32 → PMem.M α} (hb : PMem.inBridgeN a 4 = false)
    (h : Triple (MemIs s₁ M) (f (Binary32.ofBits (w32 M a.toNat))) Q) :
    Triple (MemIs s₁ M) (PMem.ldF32 a >>= f) Q :=
  Triple.bind_val (fun s hs => by rw [ldF32_run hb, hs.2]) h

theorem Triple.ldBits_mem {α : Type} {s₁ : PMem.Mem} {M : ByteArray} {Q : α → PMem.Mem → Prop} {a : UInt64}
    {o : Nat} {f : UInt64 → PMem.M α} (hb : PMem.inBridge a = false) (ho : o < 8)
    (h : Triple (MemIs s₁ M) (f (bitOf (M.get! a.toNat) o)) Q) :
    Triple (MemIs s₁ M) (PMem.ldBits a o 1 >>= f) Q :=
  Triple.bind_val (fun s hs => by rw [ldBits_run hb ho, hs.2]) h

/-- A step that changes only the memory, by `g`. -/
theorem Triple.mem_step {α β : Type} {s₁ : PMem.Mem} {M : ByteArray} {Q : β → PMem.Mem → Prop} {x : PMem.M α}
    {f : α → PMem.M β} {c : α} (g : ByteArray → ByteArray)
    (hx : ∀ s : PMem.Mem, x.run s = (c, { s with m := g s.m })) (h : Triple (MemIs s₁ (g M)) (f c) Q) :
    Triple (MemIs s₁ M) (x >>= f) Q := fun s hs => by
  rw [run_bind', hx s]
  exact h _ ⟨by have := hs.1; rw [← this], by show g s.m = g M; rw [hs.2]⟩

theorem Triple.stF32_mem {α : Type} {s₁ : PMem.Mem} {M : ByteArray} {Q : α → PMem.Mem → Prop} {a : UInt64}
    {v : Binary32} {f : PUnit → PMem.M α} (hb : PMem.inBridgeN a 4 = false) (hn : a.toNat + 4 < 2 ^ 64)
    (h : Triple (MemIs s₁ (set4 M a.toNat (Binary32.toBits v))) (f ()) Q) :
    Triple (MemIs s₁ M) (PMem.stF32 a v >>= f) Q :=
  Triple.mem_step (fun m => set4 m a.toNat (Binary32.toBits v)) (fun _ => stF32_run hb hn) h

theorem Triple.stB_mem {α : Type} {s₁ : PMem.Mem} {M : ByteArray} {Q : α → PMem.Mem → Prop} {a : UInt64}
    {v : Bool} {f : PUnit → PMem.M α} (hb : PMem.inBridge a = false)
    (h : Triple (MemIs s₁ (M.set! a.toNat (if v then 1 else 0))) (f ()) Q) :
    Triple (MemIs s₁ M) (PMem.stB a v >>= f) Q :=
  Triple.mem_step (fun m => m.set! a.toNat (if v then 1 else 0)) (fun _ => stB_run hb) h

theorem Triple.stBits_mem {α : Type} {s₁ : PMem.Mem} {M : ByteArray} {Q : α → PMem.Mem → Prop} {a : UInt64}
    {o : Nat} {v : UInt64} {f : PUnit → PMem.M α} (hb : PMem.inBridge a = false) (ho : o < 8)
    (h : Triple (MemIs s₁ (M.set! a.toNat (setBit (M.get! a.toNat) o (v.toNat % 2 = 1)))) (f ()) Q) :
    Triple (MemIs s₁ M) (PMem.stBits a o 1 v >>= f) Q :=
  Triple.mem_step (fun m => m.set! a.toNat (setBit (m.get! a.toNat) o (v.toNat % 2 = 1)))
    (fun _ => stBits_run hb ho) h

/-- `MemIs` gives the agreement with `s₁` outside the bytes where `M` differs from `s₁`'s memory. -/
theorem MemIs.agree {s₁ s : PMem.Mem} {M : ByteArray} {W : Nat → Prop} (h : MemIs s₁ M s)
    (hsz : M.size = s₁.m.size) (hb : ∀ j, ¬ W j → M.get! j = s₁.m.get! j) : Agree s₁ s W :=
  ⟨by rw [h.2, hsz], fun j hj => by rw [h.2, hb j hj], h.1⟩

end Corpus.Hoare
