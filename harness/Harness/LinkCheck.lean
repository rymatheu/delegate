import Harness.Link

/-! # Checkers for the formal link (docs/10-formal-link.md)

Two Boolean checkers, each proved sound against `Harness/Link.lean`'s semantics:

* `transportOK`: two clauses, read in two environments of one system (the system's own, or a
  child's at a lag), are the same formula once every field is replaced by the signal the wire
  delivers to it. This is the case of every clause `compose` copies, renames or fixes into the
  composite's contract. Sound: `transport_sound`, then `own_loopDis` and `copy_cover`.
* `rangeCheck`: an obligation that is a conjunction of range atoms on signals (`x ≤ c`, `c ≤ x`,
  `<`, `|x| ≤ c`, `|x| < c`, `finite x`, with literal bounds), implied by cited clauses of the
  same kind on the same signals, bounds compared as exact integers (binary32 values scaled by
  2^149). Sound: `rangeCheck_sound`, which gives `CitedDis`.

Both read the signals through `slotSig`, the wiring of `Consistent` (`slotSig_sound`). Facts
about `Float32` are the fields of `FloatFacts`, an explicit hypothesis. -/

namespace Harness.Link

open Harness

/-! ## Binary32 bit patterns as exact numbers -/

/-- The exponent field is not all ones: not an infinity, not a NaN. -/
def fin32 (b : UInt32) : Bool := (b.toNat / 2 ^ 23) % 256 != 255

/-- The magnitude of a finite binary32 bit pattern, times 2^149 (an integer). -/
def mag32 (b : UInt32) : Nat :=
  let e := (b.toNat / 2 ^ 23) % 256
  let m := b.toNat % 2 ^ 23
  if e = 0 then m else (m + 2 ^ 23) * 2 ^ (e - 1)

/-- The value of a finite binary32 bit pattern, times 2^149. -/
def val32 (b : UInt32) : Int :=
  if b.toNat / 2 ^ 31 = 0 then (mag32 b : Int) else -(mag32 b : Int)

/-- The bit pattern with the sign flipped (IEEE negation). -/
def neg32 (b : UInt32) : UInt32 := b ^^^ 0x80000000

/-- The bit pattern with the sign cleared (IEEE absolute value). -/
def abs32 (b : UInt32) : UInt32 := b &&& 0x7fffffff

/-- The binary32 bit pattern of a natural number below 2^24 (exactly representable). -/
def smallBits (n : Nat) : UInt32 :=
  if n = 0 then 0
  else UInt32.ofNat ((Nat.log2 n + 127) * 2 ^ 23 + (n * 2 ^ (23 - Nat.log2 n) - 2 ^ 23))

/-- The facts about Lean's `Float32` the checkers use. Each is a property of IEEE 754 binary32
arithmetic as the C library computes it; none is provable in core Lean, where `Float32` is
opaque, so the structure is a hypothesis wherever it is used. -/
structure FloatFacts : Prop where
  roundtrip : ∀ x : Float32, Float32.ofBits x.toBits = x
  le_trans : ∀ x y z : Float32, x ≤ y → y ≤ z → x ≤ z
  lt_of_lt_of_le : ∀ x y z : Float32, x < y → y ≤ z → x < z
  lt_of_le_of_lt : ∀ x y z : Float32, x ≤ y → y < z → x < z
  le_of_lt : ∀ x y : Float32, x < y → x ≤ y
  le_of_abs_le : ∀ x y : Float32, x.abs ≤ y → x ≤ y
  lt_of_abs_lt : ∀ x y : Float32, x.abs < y → x < y
  neg_le_of_abs_le : ∀ x y : Float32, x.abs ≤ y → -y ≤ x
  neg_lt_of_abs_lt : ∀ x y : Float32, x.abs < y → -y < x
  abs_le_of : ∀ x y : Float32, -y ≤ x → x ≤ y → x.abs ≤ y
  abs_lt_of : ∀ x y : Float32, -y < x → x < y → x.abs < y
  neg_ofBits : ∀ b : UInt32, -(Float32.ofBits b) = Float32.ofBits (neg32 b)
  abs_ofBits : ∀ b : UInt32, (Float32.ofBits b).abs = Float32.ofBits (abs32 b)
  isFinite_ofBits : ∀ b : UInt32, (Float32.ofBits b).isFinite = fin32 b
  lit_le : ∀ a b : UInt32, fin32 a = true → fin32 b = true → val32 a ≤ val32 b →
    Float32.ofBits a ≤ Float32.ofBits b
  lit_lt : ∀ a b : UInt32, fin32 a = true → fin32 b = true → val32 a < val32 b →
    Float32.ofBits a < Float32.ofBits b
  finite_of_le_le : ∀ (x : Float32) (a b : UInt32), Float32.ofBits a ≤ x →
    x ≤ Float32.ofBits b → fin32 a = true → fin32 b = true → x.isFinite = true
  le_of_beq : ∀ x y : Float32, (x == y) = true → x ≤ y
  ge_of_beq : ∀ x y : Float32, (x == y) = true → y ≤ x
  beq_of_val : ∀ a b : UInt32, fin32 a = true → fin32 b = true → val32 a = val32 b →
    (Float32.ofBits a == Float32.ofBits b) = true
  u32_small : ∀ w : UInt32, w.toNat < 2 ^ 24 → w.toFloat32 = Float32.ofBits (smallBits w.toNat)

/-! ## Signals -/

/-- What a field of an environment of the system holds at the reference tick `t`: an input of
the system `d` ticks before `t`, a parameter of the system, an output of child `j` `d` ticks
before `t`, or a constant. -/
inductive Sig where
  | cin (q d : Nat)
  | cpar (q : Nat)
  | cout (j f d : Nat)
  | const (w : UInt32)
  deriving DecidableEq, Repr

def Sig.cst : Sig → Option UInt32
  | .const w => some w
  | _ => none

/-- The word a signal holds at reference tick `t`. -/
def sigWord (r : Run) (t : Nat) : Sig → UInt32
  | .cin q d => (r.root.input (t - d))[q]!
  | .cpar q => r.root.params[q]!
  | .cout j f d => ((r.kid j).root.output (t - d))[f]!
  | .const w => w

/-- An environment of the system: its own at the reference tick, or child `j`'s `d` ticks
before it. -/
inductive Ctx where
  | sys
  | kid (j d : Nat)
  deriving DecidableEq, Repr

def ctxEnv (r : Run) (t : Nat) : Ctx → Array UInt32
  | .sys => r.root.env t
  | .kid j d => (r.kid j).root.env (t - d)

/-- A child parameter's source, as `Running.init` reads it (`fetch #[] params #[] #[]`). -/
def srcParamSig : Src → Option Sig
  | .param q => some (.cpar q)
  | .const w => some (.const w)
  | _ => none

/-- A child input's source, for child `j` read `d` ticks before the reference tick; `z`: the
reference tick is 0. A `prev` source is read only at lag 0: its initial value at tick 0, the
output of the tick before otherwise. -/
def srcInputSig (s : CSys) (z : Bool) (j d : Nat) : Src → Option Sig
  | .input q => some (.cin q d)
  | .param q => some (.cpar q)
  | .const w => some (.const w)
  | .out j' f => if j' < j then some (.cout j' f d) else none
  | .prev m =>
    if m < s.prevs.size ∧ d = 0 then
      if z then some (.const (s.prevs[m]!).init)
      else if (s.prevs[m]!).child < s.children.size then
        some (.cout (s.prevs[m]!).child (s.prevs[m]!).field 1)
      else none
    else none

/-- A system output's source. -/
def srcOutputSig (s : CSys) : Src → Option Sig
  | .input q => some (.cin q 0)
  | .param q => some (.cpar q)
  | .const w => some (.const w)
  | .out j f => if j < s.children.size then some (.cout j f 0) else none
  | .prev _ => none

/-- The signal at slot `k` of an environment (`none`: not resolved). -/
def slotSig (s : CSys) (z : Bool) : Ctx → Nat → Option Sig
  | .sys, k =>
    let P := s.view.m.params.size
    let I := s.view.m.input.size
    let O := s.view.m.output.size
    if k < P then some (.cpar k)
    else if k < P + I then some (.cin (k - P) 0)
    else if k < P + I + O then
      (if k - (P + I) < s.outputs.size then srcOutputSig s (s.outputs[k - (P + I)]!) else none)
    else none
  | .kid j d, k =>
    if j < s.children.size then
      let ch := s.children[j]!
      let v := (child s j).view.m
      if k < v.params.size then srcParamSig (ch.params[k]!)
      else if k < v.params.size + v.input.size then
        srcInputSig s z j d (ch.input[k - v.params.size]!)
      else if k < v.params.size + v.input.size + v.output.size then
        some (.cout j (k - (v.params.size + v.input.size)) d)
      else none
    else none

theorem env3_left {a b c : Array UInt32} {k : Nat} (h : k < a.size) :
    (a ++ b ++ c)[k]! = a[k]! := by
  rw [append_left! _ _ (by simp; omega), append_left! _ _ h]

theorem env3_mid {a b c : Array UInt32} {k : Nat} (h1 : a.size ≤ k) (h2 : k < a.size + b.size) :
    (a ++ b ++ c)[k]! = b[k - a.size]! := by
  rw [append_left! _ _ (by simp; omega), append_right! _ _ h1]

theorem env3_right {a b c : Array UInt32} {k : Nat} (h : a.size + b.size ≤ k) :
    (a ++ b ++ c)[k]! = c[k - (a.size + b.size)]! := by
  rw [append_right! _ _ (by simp; omega)]
  simp

/-- On a behavior, the slot of an environment holds the word of its signal. -/
theorem slotSig_sound {exe : Checked → Trace → Prop} {s : CSys} {r : Run}
    (hb : Beh exe (.system s) r) {z : Bool} {t : Nat} (hz : z = true ↔ t = 0) {ctx : Ctx}
    (hd : ∀ j d, ctx = .kid j d → d ≤ t) {k : Nat} {sg : Sig}
    (h : slotSig s z ctx k = some sg) : (ctxEnv r t ctx)[k]! = sigWord r t sg := by
  have hc := Beh.consistent hb
  have hsz := Beh.sized hb
  obtain ⟨_, hpar, hin, hout⟩ := hc
  cases ctx with
  | sys =>
    simp only [slotSig] at h
    simp only [ctxEnv, Trace.env]
    obtain ⟨hP, hIO⟩ := hsz
    obtain ⟨hI, hO⟩ := hIO t
    simp only [CNode.view] at hP hI hO
    split at h
    · cases h; rw [env3_left (by omega)]; rfl
    · split at h
      · cases h; rw [env3_mid (by omega) (by omega)]; simp [sigWord, hP]
      · split at h
        · split at h
          · rename_i h3 h4
            rw [env3_right (by omega), hout t, map! _ _ (by rw [hP, hI]; omega)]
            rw [hP, hI]
            generalize hsrc : s.outputs[k - (s.view.m.params.size + s.view.m.input.size)]! = src
              at h
            cases src with
            | input q => cases h; rfl
            | param q => cases h; rfl
            | const w => cases h; rfl
            | out j f =>
              simp only [srcOutputSig] at h
              split at h
              · cases h; rename_i hj
                simp only [fetch, sigWord]
                rw [outsUpTo, ofFn! _ hj]
                cases r; rfl
              · cases h
            | prev _ => cases h
          · cases h
        · cases h
  | kid j d =>
    have hdt := hd j d rfl
    simp only [slotSig] at h
    split at h
    · rename_i hj
      have hkid := Beh.sized (Beh.kid hb hj)
      obtain ⟨hPc, hIOc⟩ := hkid
      obtain ⟨hIc, hOc⟩ := hIOc (t - d)
      simp only [ctxEnv, Trace.env]
      split at h
      · rename_i hk
        have hps : (s.children[j]!).params.size = (child s j).view.m.params.size := by
          rw [← hPc, hpar j hj, Array.size_map]
        rw [env3_left (by rw [hPc]; exact hk), hpar j hj, map! _ _ (by rw [hps]; exact hk)]
        generalize hsrc : (s.children[j]!).params[k]! = src at h
        cases src with
        | param q => cases h; rfl
        | const w => cases h; rfl
        | input _ => cases h
        | out _ _ => cases h
        | prev _ => cases h
      · split at h
        · rename_i hk1 hk2
          have his : (s.children[j]!).input.size = (child s j).view.m.input.size := by
            rw [← hIc, hin j hj (t - d), Array.size_map]
          rw [env3_mid (by rw [hPc]; omega) (by rw [hPc, hIc]; omega), hin j hj (t - d),
            hPc, map! _ _ (by rw [his]; omega)]
          generalize hsrc : (s.children[j]!).input[k - (child s j).view.m.params.size]! = src
            at h
          cases src with
          | input q => cases h; rfl
          | param q => cases h; rfl
          | const w => cases h; rfl
          | out j' f =>
            simp only [srcInputSig] at h
            split at h
            · cases h; rename_i hj'
              simp only [fetch, sigWord]
              rw [outsUpTo, ofFn! _ hj']
              cases r; rfl
            · cases h
          | prev m =>
            simp only [srcInputSig] at h
            split at h
            · rename_i hm
              obtain ⟨hm, hd0⟩ := hm
              subst hd0
              simp only [fetch, Nat.sub_zero]
              split at h
              · cases h
                rename_i hzt
                have ht0 : t = 0 := hz.mp hzt
                subst ht0
                simp only [prevAt, sigWord]
                rw [map! _ _ hm]
              · split at h
                · cases h
                  rename_i hzt hc
                  have ht0 : t ≠ 0 := fun h0 => hzt (hz.mpr h0)
                  obtain ⟨t', rfl⟩ : ∃ t', t = t' + 1 := ⟨t - 1, by omega⟩
                  simp only [prevAt, sigWord]
                  rw [map! _ _ hm]; simp only [outsUpTo]; rw [ofFn! _ hc]
                  cases r; simp [Run.kid, Run.kids]
                · cases h
            · cases h
        · split at h
          · cases h
            rename_i hk1 hk2 hk3
            rw [env3_right (by rw [hPc, hIc]; omega), hPc, hIc]
            rfl
          · cases h
    · cases h

/-! ## Matching two formulas through the wires -/

/-- The two formulas are the same, field by field, once each field of the first is replaced by
its key under `f` and each field of the second by its key under `g`; a field of the first whose
key is a constant may stand against the literal that constant reads as (what `fix`
substitutes). -/
def match2 {K : Type} [DecidableEq K] (cst : K → Option UInt32) (f g : Nat → Option K) :
    Expr → Expr → Bool
  | .ref _ k t, .ref _ k' t' =>
    match f k, g k' with
    | some a, some b => decide (a = b) && decide (t = t')
    | _, _ => false
  | .ref _ k t, .lit b =>
    match f k with
    | some a => match cst a with
      | some w => decide (t ≠ .bool) && decide (b = (Expr.wordToF32 t w).toBits)
      | none => false
    | none => false
  | .ref _ k t, .blit b =>
    match f k with
    | some a => match cst a with
      | some w => decide (t = .bool) && decide (b = (w != 0))
      | none => false
    | none => false
  | .lit b, .lit b' => decide (b = b')
  | .blit b, .blit b' => decide (b = b')
  | .add a b, .add a' b' => match2 cst f g a a' && match2 cst f g b b'
  | .sub a b, .sub a' b' => match2 cst f g a a' && match2 cst f g b b'
  | .mul a b, .mul a' b' => match2 cst f g a a' && match2 cst f g b b'
  | .div a b, .div a' b' => match2 cst f g a a' && match2 cst f g b b'
  | .le a b, .le a' b' => match2 cst f g a a' && match2 cst f g b b'
  | .lt a b, .lt a' b' => match2 cst f g a a' && match2 cst f g b b'
  | .eq a b, .eq a' b' => match2 cst f g a a' && match2 cst f g b b'
  | .and a b, .and a' b' => match2 cst f g a a' && match2 cst f g b b'
  | .or a b, .or a' b' => match2 cst f g a a' && match2 cst f g b b'
  | .neg a, .neg a' => match2 cst f g a a'
  | .abs a, .abs a' => match2 cst f g a a'
  | .not a, .not a' => match2 cst f g a a'
  | .finite a, .finite a' => match2 cst f g a a'
  | _, _ => false

theorem eval_ref (env : Array UInt32) (n : String) (k : Nat) (t : FieldType) :
    Expr.eval env (.ref n k t) =
      if t = .bool then .bool (env[k]! != 0) else .num (Expr.wordToF32 t env[k]!) := by
  cases t <;> rfl

theorem match2_sound (ff : FloatFacts) {K : Type} [DecidableEq K] (cst : K → Option UInt32)
    (W : K → UInt32) (hW : ∀ a w, cst a = some w → W a = w) {f g : Nat → Option K}
    {env1 env2 : Array UInt32} (hf : ∀ k a, f k = some a → env1[k]! = W a)
    (hg : ∀ k a, g k = some a → env2[k]! = W a) :
    ∀ e1 e2, match2 cst f g e1 e2 = true → Expr.eval env1 e1 = Expr.eval env2 e2 := by
  intro e1
  induction e1 with
  | ref n k t =>
    intro e2 h
    cases e2 with
    | ref n' k' t' =>
      simp only [match2] at h
      cases hfk : f k with
      | none => simp [hfk] at h
      | some a =>
        cases hgk : g k' with
        | none => simp [hfk, hgk] at h
        | some b =>
          simp [hfk, hgk] at h
          obtain ⟨rfl, rfl⟩ := h
          rw [eval_ref, eval_ref, hf k a hfk, hg k' a hgk]
    | lit b =>
      simp only [match2] at h
      cases hfk : f k with
      | none => simp [hfk] at h
      | some a =>
        cases hca : cst a with
        | none => simp [hfk, hca] at h
        | some w =>
          simp [hfk, hca] at h
          obtain ⟨ht, rfl⟩ := h
          rw [eval_ref, hf k a hfk, hW a w hca, ite_eq_right ht]
          show Expr.Val.num _ = Expr.Val.num (Float32.ofBits _)
          rw [ff.roundtrip]
    | blit b =>
      simp only [match2] at h
      cases hfk : f k with
      | none => simp [hfk] at h
      | some a =>
        cases hca : cst a with
        | none => simp [hfk, hca] at h
        | some w =>
          simp [hfk, hca] at h
          obtain ⟨rfl, rfl⟩ := h
          rw [eval_ref, hf k a hfk, hW a w hca, ite_eq_left rfl]
          rfl
    | _ => simp [match2] at h
  | lit b =>
    intro e2 h
    cases e2 <;> simp [match2] at h
    subst h; rfl
  | blit b =>
    intro e2 h
    cases e2 <;> simp [match2] at h
    subst h; rfl
  | var n =>
    intro e2 h
    cases e2 <;> simp [match2] at h
  | add a b iha ihb | sub a b iha ihb | mul a b iha ihb | div a b iha ihb
  | le a b iha ihb | lt a b iha ihb | eq a b iha ihb | and a b iha ihb | or a b iha ihb =>
    intro e2 h
    cases e2 <;> simp [match2] at h
    all_goals
      simp only [Expr.eval]
      rw [iha _ h.1, ihb _ h.2]
  | neg a iha | abs a iha | not a iha | finite a iha =>
    intro e2 h
    cases e2 <;> simp [match2] at h
    all_goals
      simp only [Expr.eval]
      rw [iha _ h]

/-- Two formulas read in two environments of the system agree through the wires, at every
reference tick (both cases of the first tick checked). -/
def transportOK (s : CSys) (c1 : Ctx) (e1 : Expr) (c2 : Ctx) (e2 : Expr) : Bool :=
  [true, false].all fun z => match2 Sig.cst (slotSig s z c1) (slotSig s z c2) e1 e2

theorem transport_sound (ff : FloatFacts) {exe : Checked → Trace → Prop} {s : CSys} {r : Run}
    (hb : Beh exe (.system s) r) {c1 c2 : Ctx} {e1 e2 : Expr} (t : Nat)
    (hd1 : ∀ j d, c1 = .kid j d → d ≤ t) (hd2 : ∀ j d, c2 = .kid j d → d ≤ t)
    (h : transportOK s c1 e1 c2 e2 = true) :
    Expr.eval (ctxEnv r t c1) e1 = Expr.eval (ctxEnv r t c2) e2 := by
  have hz : decide (t = 0) = true ↔ t = 0 := by simp
  have hm : match2 Sig.cst (slotSig s (decide (t = 0)) c1) (slotSig s (decide (t = 0)) c2) e1 e2
      = true := by
    simp only [transportOK, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
    by_cases h0 : t = 0 <;> simp [h0, h.1, h.2]
  exact match2_sound ff Sig.cst (sigWord r t) (fun a w ha => by cases a <;> simp [Sig.cst] at ha; subst ha; rfl)
    (fun k a hk => slotSig_sound hb hz hd1 hk) (fun k a hk => slotSig_sound hb hz hd2 hk) _ _ hm

/-- A child's assumption clause that is a composite assumption clause read through the wires
is discharged by the composite's assumption. -/
theorem own_loopDis (ff : FloatFacts) {exe : Checked → Trace → Prop} {s : CSys} {i k q : Nat}
    (hq : q < s.view.assume.size)
    (h : transportOK s (.kid i 0) ((child s i).view.assume[k]!).expr .sys
      (s.view.assume[q]!).expr = true) : OpenDis exe s i k := by
  intro r hb t hsys _ _
  have he := transport_sound ff hb t (fun _ _ hc => by cases hc; omega) (fun _ _ hc => by cases hc) h
  simp only [ctxEnv, Nat.sub_zero] at he
  simp only [Expr.holds]
  rw [he]
  exact hsys t (Nat.le_refl t) q hq

/-- A composite guarantee clause that is a child's guarantee clause read through the wires is
covered. -/
theorem copy_cover (ff : FloatFacts) {exe : Checked → Trace → Prop} {s : CSys} {i k k' : Nat}
    (hi : i < s.children.size) (hk' : k' < (child s i).view.guarantee.size)
    (h : transportOK s (.kid i 0) ((child s i).view.guarantee[k']!).expr .sys
      (s.view.guarantee[k]!).expr = true) : OpenCover exe s k := by
  intro r hb t _ hkids
  have he := transport_sound ff hb t (fun _ _ hc => by cases hc; omega) (fun _ _ hc => by cases hc) h
  simp only [ctxEnv, Nat.sub_zero] at he
  simp only [Expr.holds]
  rw [← he]
  exact Deep.guarantee (hkids i hi t (Nat.le_refl t)) k' hk'

/-! ## Range atoms -/

inductive Form where
  | le | lt | ge | gt | absle | abslt | fin | eq
  deriving DecidableEq, Repr

/-- `x ≤ c`, `x < c`, `c ≤ x`, `c < x`, `|x| ≤ c`, `|x| < c`, `finite x`, `x = c` (IEEE
equality), on the number `x`. -/
def formSem (x : Float32) (c : UInt32) : Form → Prop
  | .le => x ≤ Float32.ofBits c
  | .lt => x < Float32.ofBits c
  | .ge => Float32.ofBits c ≤ x
  | .gt => Float32.ofBits c < x
  | .absle => x.abs ≤ Float32.ofBits c
  | .abslt => x.abs < Float32.ofBits c
  | .fin => x.isFinite = true
  | .eq => (x == Float32.ofBits c) = true

/-- A range atom on slot `k` of type `ty`. -/
structure Atom where
  slot : Nat
  ty : FieldType
  form : Form
  c : UInt32
  deriving Repr

/-- A literal bound: a binary32 literal or its negation. -/
def litBits : Expr → Option UInt32
  | .lit b => some b
  | .neg (.lit b) => some (neg32 b)
  | _ => none

def parseRel (strict : Bool) (a b : Expr) : Option Atom :=
  match a with
  | .ref _ k t => (litBits b).map fun c => ⟨k, t, if strict then .lt else .le, c⟩
  | .abs (.ref _ k t) => (litBits b).map fun c => ⟨k, t, if strict then .abslt else .absle, c⟩
  | _ => match b with
    | .ref _ k t => (litBits a).map fun c => ⟨k, t, if strict then .gt else .ge, c⟩
    | _ => none

def parseEq (a b : Expr) : Option Atom :=
  match a with
  | .ref _ k t => (litBits b).map fun c => ⟨k, t, .eq, c⟩
  | _ => none

/-- The atom an expression is, if it is one. -/
def parseAtom : Expr → Option Atom
  | .le a b => parseRel false a b
  | .lt a b => parseRel true a b
  | .eq a b => parseEq a b
  | .finite (.ref _ k t) => some ⟨k, t, .fin, 0⟩
  | _ => none

theorem litBits_sound (ff : FloatFacts) {env : Array UInt32} {e : Expr} {c : UInt32}
    (h : litBits e = some c) : (Expr.eval env e).toF32 = Float32.ofBits c := by
  unfold litBits at h
  split at h
  · cases h; rfl
  · cases h
    show -(Float32.ofBits _) = _
    exact ff.neg_ofBits _
  · cases h

theorem litBits_num (ff : FloatFacts) {env : Array UInt32} {e : Expr} {c : UInt32}
    (h : litBits e = some c) : Expr.eval env e = .num (Float32.ofBits c) := by
  unfold litBits at h
  split at h
  · cases h; rfl
  · cases h
    show Expr.Val.num (-(Float32.ofBits _)) = _
    rw [ff.neg_ofBits]
  · cases h

theorem beq_bool_iff (t : FieldType) : (t == .bool) = true ↔ t = .bool := by
  cases t <;> decide

theorem eval_ref_num (env : Array UInt32) (n : String) (k : Nat) (t : FieldType)
    (ht : t ≠ .bool) : (Expr.eval env (.ref n k t)).toF32 = Expr.wordToF32 t env[k]! := by
  rw [eval_ref, ite_eq_right ht]; rfl

theorem decide_eq_true_iff' {p : Prop} [Decidable p] : (decide p = true) ↔ p := decide_eq_true_iff

/-- An atom holds exactly when its expression does. -/
theorem parseAtom_sound (ff : FloatFacts) {env : Array UInt32} {e : Expr} {a : Atom}
    (h : parseAtom e = some a) (ht : a.ty ≠ .bool) :
    Expr.holds env e = true ↔ formSem (Expr.wordToF32 a.ty env[a.slot]!) a.c a.form := by
  have rel : ∀ (strict : Bool) (x y : Expr), parseRel strict x y = some a →
      (Expr.Val.toBool (.bool (if strict then decide ((Expr.eval env x).toF32 < (Expr.eval env y).toF32)
        else decide ((Expr.eval env x).toF32 ≤ (Expr.eval env y).toF32))) = true ↔
        formSem (Expr.wordToF32 a.ty env[a.slot]!) a.c a.form) := by
    intro strict x y hr
    unfold parseRel at hr
    split at hr
    · rename_i n k t
      cases hl : litBits y with
      | none => simp [hl] at hr
      | some c =>
        simp [hl] at hr
        subst hr
        rw [litBits_sound ff hl, eval_ref_num _ _ _ _ ht]
        cases strict <;> simp [Expr.Val.toBool, formSem]
    · rename_i n k t
      cases hl : litBits y with
      | none => simp [hl] at hr
      | some c =>
        simp [hl] at hr
        subst hr
        rw [litBits_sound ff hl]
        have : (Expr.eval env (.abs (.ref n k t))).toF32 = (Expr.wordToF32 t env[k]!).abs := by
          show Float32.abs (Expr.eval env (.ref n k t)).toF32 = _
          rw [eval_ref_num _ _ _ _ ht]
        rw [this]
        cases strict <;> simp [Expr.Val.toBool, formSem]
    · split at hr
      · rename_i n k t _
        cases hl : litBits x with
        | none => simp [hl] at hr
        | some c =>
          simp [hl] at hr
          subst hr
          rw [litBits_sound ff hl, eval_ref_num _ _ _ _ ht]
          cases strict <;> simp [Expr.Val.toBool, formSem]
      · cases hr
  unfold parseAtom at h
  split at h
  · exact rel false _ _ h
  · exact rel true _ _ h
  · rename_i x y
    unfold parseEq at h
    split at h
    · rename_i n k t
      cases hl : litBits y with
      | none => simp [hl] at h
      | some c =>
        simp [hl] at h
        subst h
        have hr : Expr.eval env (.ref n k t) = .num (Expr.wordToF32 t env[k]!) := by
          rw [eval_ref, ite_eq_right ht]
        show (match Expr.eval env (Expr.ref n k t), Expr.eval env y with
          | .num x, .num y => Expr.Val.bool (x == y)
          | .bool x, .bool y => .bool (x == y)
          | _, _ => .bool false).toBool = true ↔ _
        rw [hr, litBits_num ff hl]
        simp [Expr.Val.toBool, formSem]
    · cases h
  · cases h
    simp only at ht
    simp only [Expr.holds, Expr.eval]
    rw [ite_eq_right (by rwa [beq_bool_iff])]
    simp [Expr.Val.toBool, Expr.Val.toF32, formSem]
  · cases h

/-- An atom on a signal. -/
structure SAtom where
  sig : Sig
  ty : FieldType
  form : Form
  c : UInt32
  deriving Repr

def SAtom.sem (r : Run) (t : Nat) (a : SAtom) : Prop :=
  formSem (Expr.wordToF32 a.ty (sigWord r t a.sig)) a.c a.form

def resolveAtom (s : CSys) (z : Bool) (ctx : Ctx) (a : Atom) : Option SAtom :=
  if a.ty = .bool then none else (slotSig s z ctx a.slot).map fun sg => ⟨sg, a.ty, a.form, a.c⟩

/-- An upper bound `x ≤ c` (`x < c` when strict) the atom gives. -/
def upper (a : SAtom) : Option (Bool × UInt32) :=
  match a.form with
  | .le => some (false, a.c)
  | .lt => some (true, a.c)
  | .absle => some (false, a.c)
  | .abslt => some (true, a.c)
  | .eq => some (false, a.c)
  | _ => none

/-- A lower bound `c ≤ x` (`c < x` when strict) the atom gives. -/
def lower (a : SAtom) : Option (Bool × UInt32) :=
  match a.form with
  | .ge => some (false, a.c)
  | .gt => some (true, a.c)
  | .absle => some (false, neg32 a.c)
  | .abslt => some (true, neg32 a.c)
  | .eq => some (false, a.c)
  | _ => none

def bnd (strict : Bool) (x : Float32) (c : UInt32) : Prop :=
  if strict then x < Float32.ofBits c else x ≤ Float32.ofBits c

def bndL (strict : Bool) (x : Float32) (c : UInt32) : Prop :=
  if strict then Float32.ofBits c < x else Float32.ofBits c ≤ x

theorem upper_sound (ff : FloatFacts) {x : Float32} {a : SAtom} {st : Bool} {c : UInt32}
    (hs : formSem x a.c a.form) (h : upper a = some (st, c)) : bnd st x c := by
  unfold upper at h
  split at h <;> (try cases h)
  all_goals rename_i hf; rw [hf] at hs; simp only [formSem] at hs; simp only [bnd]
  · exact hs
  · exact hs
  · exact ff.le_of_abs_le _ _ hs
  · exact ff.lt_of_abs_lt _ _ hs
  · exact ff.le_of_beq _ _ hs

theorem lower_sound (ff : FloatFacts) {x : Float32} {a : SAtom} {st : Bool} {c : UInt32}
    (hs : formSem x a.c a.form) (h : lower a = some (st, c)) : bndL st x c := by
  unfold lower at h
  split at h <;> (try cases h)
  all_goals rename_i hf; rw [hf] at hs; simp only [formSem] at hs; simp only [bndL]
  · exact hs
  · exact hs
  · rw [← ff.neg_ofBits]; exact ff.neg_le_of_abs_le _ _ hs
  · rw [← ff.neg_ofBits]; exact ff.neg_lt_of_abs_lt _ _ hs
  · exact ff.ge_of_beq _ _ hs

def sameAs (sg : Sig) (ty : FieldType) (a : SAtom) : Bool := decide (a.sig = sg) && decide (a.ty = ty)

/-- `x ≤ c₂` (`x < c₂` when strict) follows from one of the facts. -/
def proveUp (facts : List SAtom) (sg : Sig) (ty : FieldType) (c2 : UInt32) (strict : Bool) :
    Bool :=
  facts.any fun a => sameAs sg ty a && match upper a with
    | some (st, c1) => fin32 c1 && fin32 c2 &&
        (if strict && !st then decide (val32 c1 < val32 c2) else decide (val32 c1 ≤ val32 c2))
    | none => false

/-- `c₂ ≤ x` (`c₂ < x` when strict) follows from one of the facts. -/
def proveLo (facts : List SAtom) (sg : Sig) (ty : FieldType) (c2 : UInt32) (strict : Bool) :
    Bool :=
  facts.any fun a => sameAs sg ty a && match lower a with
    | some (st, c1) => fin32 c1 && fin32 c2 &&
        (if strict && !st then decide (val32 c2 < val32 c1) else decide (val32 c2 ≤ val32 c1))
    | none => false

def anyBound (facts : List SAtom) (sg : Sig) (ty : FieldType)
    (side : SAtom → Option (Bool × UInt32)) : Bool :=
  facts.any fun a => sameAs sg ty a && match side a with
    | some (_, c) => fin32 c
    | none => false

/-- The goal atom follows from the facts on the same signal. -/
def proveAtom (facts : List SAtom) (g : SAtom) : Bool :=
  match g.form with
  | .le => proveUp facts g.sig g.ty g.c false
  | .lt => proveUp facts g.sig g.ty g.c true
  | .ge => proveLo facts g.sig g.ty g.c false
  | .gt => proveLo facts g.sig g.ty g.c true
  | .absle => proveUp facts g.sig g.ty g.c false && proveLo facts g.sig g.ty (neg32 g.c) false
  | .abslt => proveUp facts g.sig g.ty g.c true && proveLo facts g.sig g.ty (neg32 g.c) true
  | .fin => facts.any (fun a => sameAs g.sig g.ty a && decide (a.form = .fin)) ||
      (anyBound facts g.sig g.ty upper && anyBound facts g.sig g.ty lower)
  | .eq => false

/-- The bit pattern of the number a constant word of the type reads as: itself for f32, the
exact binary32 of a u32 below 2^24. -/
def constBits (ty : FieldType) (w : UInt32) : Option UInt32 :=
  match ty with
  | .f32 => some w
  | .u32 => if w.toNat < 2 ^ 24 then some (smallBits w.toNat) else none
  | _ => none

/-- The goal atom on a constant (f32, or u32 below 2^24) holds, by exact comparison. -/
def constHolds (g : SAtom) : Bool :=
  match g.sig with
  | .const w => match constBits g.ty w with
    | some b => match g.form with
      | .le => fin32 b && fin32 g.c && decide (val32 b ≤ val32 g.c)
      | .lt => fin32 b && fin32 g.c && decide (val32 b < val32 g.c)
      | .ge => fin32 g.c && fin32 b && decide (val32 g.c ≤ val32 b)
      | .gt => fin32 g.c && fin32 b && decide (val32 g.c < val32 b)
      | .absle => fin32 (abs32 b) && fin32 g.c && decide (val32 (abs32 b) ≤ val32 g.c)
      | .abslt => fin32 (abs32 b) && fin32 g.c && decide (val32 (abs32 b) < val32 g.c)
      | .fin => fin32 b
      | .eq => fin32 b && fin32 g.c && decide (val32 b = val32 g.c)
    | none => false
  | _ => false

theorem constBits_sound (ff : FloatFacts) {ty : FieldType} {w b : UInt32}
    (h : constBits ty w = some b) : Expr.wordToF32 ty w = Float32.ofBits b := by
  cases ty with
  | f32 => simp [constBits] at h; subst h; rfl
  | u32 =>
    simp only [constBits] at h
    split at h
    · rename_i hw; cases h; exact ff.u32_small w hw
    · cases h
  | i32 => simp [constBits] at h
  | bool => simp [constBits] at h

theorem proveUp_sound (ff : FloatFacts) {r : Run} {t : Nat} {facts : List SAtom} {sg : Sig}
    {ty : FieldType} {c2 : UInt32} {strict : Bool} (hf : ∀ a, a ∈ facts → a.sem r t)
    (h : proveUp facts sg ty c2 strict = true) :
    bnd strict (Expr.wordToF32 ty (sigWord r t sg)) c2 := by
  simp only [proveUp, List.any_eq_true, Bool.and_eq_true] at h
  obtain ⟨a, ha, ⟨hsame, hb⟩⟩ := h
  simp only [sameAs, Bool.and_eq_true, decide_eq_true_eq] at hsame
  obtain ⟨rfl, rfl⟩ := hsame
  cases hu : upper a with
  | none => simp [hu] at hb
  | some p =>
    obtain ⟨st, c1⟩ := p
    simp only [hu, Bool.and_eq_true] at hb
    obtain ⟨⟨h1, h2⟩, h3⟩ := hb
    have hx := upper_sound ff (hf a ha) hu
    simp only [bnd] at hx ⊢
    cases strict <;> cases st <;> simp at h3 hx ⊢
    · exact ff.le_trans _ _ _ hx (ff.lit_le _ _ h1 h2 h3)
    · exact ff.le_trans _ _ _ (ff.le_of_lt _ _ hx) (ff.lit_le _ _ h1 h2 h3)
    · exact ff.lt_of_le_of_lt _ _ _ hx (ff.lit_lt _ _ h1 h2 h3)
    · exact ff.lt_of_lt_of_le _ _ _ hx (ff.lit_le _ _ h1 h2 h3)

theorem proveLo_sound (ff : FloatFacts) {r : Run} {t : Nat} {facts : List SAtom} {sg : Sig}
    {ty : FieldType} {c2 : UInt32} {strict : Bool} (hf : ∀ a, a ∈ facts → a.sem r t)
    (h : proveLo facts sg ty c2 strict = true) :
    bndL strict (Expr.wordToF32 ty (sigWord r t sg)) c2 := by
  simp only [proveLo, List.any_eq_true, Bool.and_eq_true] at h
  obtain ⟨a, ha, ⟨hsame, hb⟩⟩ := h
  simp only [sameAs, Bool.and_eq_true, decide_eq_true_eq] at hsame
  obtain ⟨rfl, rfl⟩ := hsame
  cases hu : lower a with
  | none => simp [hu] at hb
  | some p =>
    obtain ⟨st, c1⟩ := p
    simp only [hu, Bool.and_eq_true] at hb
    obtain ⟨⟨h1, h2⟩, h3⟩ := hb
    have hx := lower_sound ff (hf a ha) hu
    simp only [bndL] at hx ⊢
    cases strict <;> cases st <;> simp at h3 hx ⊢
    · exact ff.le_trans _ _ _ (ff.lit_le _ _ h2 h1 h3) hx
    · exact ff.le_trans _ _ _ (ff.lit_le _ _ h2 h1 h3) (ff.le_of_lt _ _ hx)
    · exact ff.lt_of_lt_of_le _ _ _ (ff.lit_lt _ _ h2 h1 h3) hx
    · exact ff.lt_of_le_of_lt _ _ _ (ff.lit_le _ _ h2 h1 h3) hx

theorem anyBound_up (ff : FloatFacts) {r : Run} {t : Nat} {facts : List SAtom} {sg : Sig}
    {ty : FieldType} (hf : ∀ a, a ∈ facts → a.sem r t) (h : anyBound facts sg ty upper = true) :
    ∃ c, fin32 c = true ∧ Expr.wordToF32 ty (sigWord r t sg) ≤ Float32.ofBits c := by
  simp only [anyBound, List.any_eq_true, Bool.and_eq_true] at h
  obtain ⟨a, ha, ⟨hsame, hb⟩⟩ := h
  simp only [sameAs, Bool.and_eq_true, decide_eq_true_eq] at hsame
  obtain ⟨rfl, rfl⟩ := hsame
  cases hu : upper a with
  | none => simp [hu] at hb
  | some p =>
    obtain ⟨st, c⟩ := p
    simp only [hu] at hb
    have hx := upper_sound ff (hf a ha) hu
    refine ⟨c, hb, ?_⟩
    simp only [bnd] at hx
    cases st <;> simp at hx
    · exact hx
    · exact ff.le_of_lt _ _ hx

theorem anyBound_lo (ff : FloatFacts) {r : Run} {t : Nat} {facts : List SAtom} {sg : Sig}
    {ty : FieldType} (hf : ∀ a, a ∈ facts → a.sem r t) (h : anyBound facts sg ty lower = true) :
    ∃ c, fin32 c = true ∧ Float32.ofBits c ≤ Expr.wordToF32 ty (sigWord r t sg) := by
  simp only [anyBound, List.any_eq_true, Bool.and_eq_true] at h
  obtain ⟨a, ha, ⟨hsame, hb⟩⟩ := h
  simp only [sameAs, Bool.and_eq_true, decide_eq_true_eq] at hsame
  obtain ⟨rfl, rfl⟩ := hsame
  cases hu : lower a with
  | none => simp [hu] at hb
  | some p =>
    obtain ⟨st, c⟩ := p
    simp only [hu] at hb
    have hx := lower_sound ff (hf a ha) hu
    refine ⟨c, hb, ?_⟩
    simp only [bndL] at hx
    cases st <;> simp at hx
    · exact hx
    · exact ff.le_of_lt _ _ hx

theorem proveAtom_sound (ff : FloatFacts) {r : Run} {t : Nat} {facts : List SAtom} {g : SAtom}
    (hf : ∀ a, a ∈ facts → a.sem r t) (h : proveAtom facts g = true) : g.sem r t := by
  simp only [SAtom.sem]
  unfold proveAtom at h
  split at h
  all_goals rename_i hform; rw [hform]; simp only [formSem]
  · simpa [bnd] using proveUp_sound ff hf h
  · simpa [bnd] using proveUp_sound ff hf h
  · simpa [bndL] using proveLo_sound ff hf h
  · simpa [bndL] using proveLo_sound ff hf h
  · simp only [Bool.and_eq_true] at h
    have hu := proveUp_sound ff hf h.1
    have hl := proveLo_sound ff hf h.2
    simp only [bnd, bndL] at hu hl
    simp at hu hl
    rw [← ff.neg_ofBits] at hl
    exact ff.abs_le_of _ _ hl hu
  · simp only [Bool.and_eq_true] at h
    have hu := proveUp_sound ff hf h.1
    have hl := proveLo_sound ff hf h.2
    simp only [bnd, bndL] at hu hl
    simp at hu hl
    rw [← ff.neg_ofBits] at hl
    exact ff.abs_lt_of _ _ hl hu
  · simp only [Bool.or_eq_true, Bool.and_eq_true, List.any_eq_true, decide_eq_true_eq] at h
    rcases h with ⟨a, ha, hsame, hfa⟩ | ⟨hu, hl⟩
    · simp only [sameAs, Bool.and_eq_true, decide_eq_true_eq] at hsame
      have := hf a ha
      simp only [SAtom.sem, hfa, formSem, hsame.1, hsame.2] at this
      exact this
    · obtain ⟨cu, hcu, hxu⟩ := anyBound_up ff hf hu
      obtain ⟨cl, hcl, hxl⟩ := anyBound_lo ff hf hl
      exact ff.finite_of_le_le _ _ _ hxl hxu hcl hcu
  · cases h

theorem constHolds_sound (ff : FloatFacts) {r : Run} {t : Nat} {g : SAtom}
    (h : constHolds g = true) : g.sem r t := by
  unfold constHolds at h
  split at h
  · rename_i w hsig
    cases hb : constBits g.ty w with
    | none => simp [hb] at h
    | some b =>
      simp only [hb] at h
      simp only [SAtom.sem, hsig, sigWord, constBits_sound ff hb]
      revert h
      cases g.form <;> simp only [formSem, Bool.and_eq_true, decide_eq_true_eq] <;> intro h
      · exact ff.lit_le _ _ h.1.1 h.1.2 h.2
      · exact ff.lit_lt _ _ h.1.1 h.1.2 h.2
      · exact ff.lit_le _ _ h.1.1 h.1.2 h.2
      · exact ff.lit_lt _ _ h.1.1 h.1.2 h.2
      · rw [ff.abs_ofBits]; exact ff.lit_le _ _ h.1.1 h.1.2 h.2
      · rw [ff.abs_ofBits]; exact ff.lit_lt _ _ h.1.1 h.1.2 h.2
      · rw [ff.isFinite_ofBits]; exact h
      · exact ff.beq_of_val _ _ h.1.1 h.1.2 h.2
  · cases h

/-! ## The range checker -/

theorem holds_conjuncts {env : Array UInt32} :
    ∀ e : Expr, (∀ e', e' ∈ e.conjuncts → Expr.holds env e' = true) → Expr.holds env e = true
  | .and a b, h => by
    simp only [Expr.conjuncts, List.mem_append] at h
    simp only [Expr.holds, Expr.eval, Expr.Val.toBool, Bool.and_eq_true]
    exact ⟨holds_conjuncts a fun e' he => h e' (Or.inl he),
      holds_conjuncts b fun e' he => h e' (Or.inr he)⟩
  | .var _, h | .ref _ _ _, h | .lit _, h | .blit _, h | .add _ _, h | .sub _ _, h
  | .mul _ _, h | .div _ _, h | .neg _, h | .abs _, h | .le _ _, h | .lt _ _, h | .eq _ _, h
  | .or _ _, h | .not _, h | .finite _, h => h _ (by simp [Expr.conjuncts])

theorem conjuncts_holds {env : Array UInt32} :
    ∀ e : Expr, Expr.holds env e = true → ∀ e', e' ∈ e.conjuncts → Expr.holds env e' = true
  | .and a b, h, e', he => by
    simp only [Expr.conjuncts, List.mem_append] at he
    simp only [Expr.holds, Expr.eval, Expr.Val.toBool, Bool.and_eq_true] at h
    rcases he with he | he
    · exact conjuncts_holds a h.1 e' he
    · exact conjuncts_holds b h.2 e' he
  | .var _, h, e', he | .ref _ _ _, h, e', he | .lit _, h, e', he | .blit _, h, e', he
  | .add _ _, h, e', he | .sub _ _, h, e', he | .mul _ _, h, e', he | .div _ _, h, e', he
  | .neg _, h, e', he | .abs _, h, e', he | .le _ _, h, e', he | .lt _ _, h, e', he
  | .eq _ _, h, e', he | .or _ _, h, e', he | .not _, h, e', he | .finite _, h, e', he => by
    simp only [Expr.conjuncts, List.mem_singleton] at he
    subst he; exact h

/-- The cited clauses usable in a case of the first tick (`z`: the reference tick is 0), with
the environment each is read in: assumption clauses of the system at the tick; guarantee
clauses of a child (not deeper instances), at lag 0, or at lag 1 after the first tick. -/
def citedFacts (s : CSys) (z : Bool) (cs : List Cite) : List (Ctx × Expr) :=
  cs.flatMap fun c => match c with
    | .assume q => (s.view.assume[q]!).expr.conjuncts.map fun e => (.sys, e)
    | .guar j [] k lag =>
      if decide (j < s.children.size) && ((z && lag == 0) || (!z && decide (lag ≤ 1))) then
        ((child s j).view.guarantee[k]!).expr.conjuncts.map fun e => (.kid j lag, e)
      else []
    | .guar _ (_ :: _) _ _ => []

/-- One conjunct of the obligation follows: it is a cited conjunct read through the wires, or a
range atom implied by the cited range atoms on the same signal, or a range atom on a constant
that holds. -/
def conjunctOK (s : CSys) (z : Bool) (i : Nat) (facts : List (Ctx × Expr)) (e : Expr) : Bool :=
  facts.any (fun p => match2 Sig.cst (slotSig s z (.kid i 0)) (slotSig s z p.1) e p.2) ||
  match (parseAtom e).bind (resolveAtom s z (.kid i 0)) with
  | some g => constHolds g ||
      proveAtom (facts.filterMap fun p => (parseAtom p.2).bind (resolveAtom s z p.1)) g
  | none => false

/-- The cited facts hold, each in its environment, at reference tick `t`. -/
def FactsHold (r : Run) (t : Nat) (facts : List (Ctx × Expr)) : Prop :=
  ∀ p, p ∈ facts → (∀ j d, p.1 = .kid j d → d ≤ t) ∧ Expr.holds (ctxEnv r t p.1) p.2 = true

theorem resolveAtom_sound (ff : FloatFacts) {exe : Checked → Trace → Prop} {s : CSys} {r : Run}
    (hb : Beh exe (.system s) r) {z : Bool} {t : Nat} (hz : z = true ↔ t = 0) {ctx : Ctx}
    (hd : ∀ j d, ctx = .kid j d → d ≤ t) {e : Expr} {a : Atom} {g : SAtom}
    (hp : parseAtom e = some a) (hr : resolveAtom s z ctx a = some g) :
    Expr.holds (ctxEnv r t ctx) e = true ↔ g.sem r t := by
  unfold resolveAtom at hr
  split at hr
  · cases hr
  · rename_i hty
    cases hs : slotSig s z ctx a.slot with
    | none => simp [hs] at hr
    | some sg =>
      simp [hs] at hr
      subst hr
      rw [parseAtom_sound ff hp hty, slotSig_sound hb hz hd hs]
      rfl

/-- One formula of the obligation (read in child `i`'s environment) follows from the facts as
a leaf: it is a fact read through the wires, or a range atom implied by the facts' range atoms
on the same signal, or a range atom on a constant that holds. -/
theorem conjunctOK_sound (ff : FloatFacts) {exe : Checked → Trace → Prop} {s : CSys} {r : Run}
    (hb : Beh exe (.system s) r) {z : Bool} {t : Nat} (hz : z = true ↔ t = 0) {i : Nat}
    {facts : List (Ctx × Expr)} (hfacts : FactsHold r t facts) {e : Expr}
    (h : conjunctOK s z i facts e = true) : Expr.holds ((r.kid i).root.env t) e = true := by
  have hatoms : ∀ a, a ∈ facts.filterMap
      (fun p => (parseAtom p.2).bind (resolveAtom s z p.1)) → a.sem r t := by
    intro a ha
    simp only [List.mem_filterMap] at ha
    obtain ⟨p, hp, hpa⟩ := ha
    obtain ⟨hd, hh⟩ := hfacts p hp
    cases hpe : parseAtom p.2 with
    | none => simp [hpe] at hpa
    | some at_ =>
      simp only [hpe, Option.bind_some] at hpa
      exact (resolveAtom_sound ff hb hz hd hpe hpa).mp hh
  have hdi : ∀ j d, Ctx.kid i 0 = .kid j d → d ≤ t := fun _ _ h => by cases h; omega
  simp only [conjunctOK, Bool.or_eq_true, List.any_eq_true] at h
  rcases h with ⟨p, hp, hm⟩ | hatom
  · obtain ⟨hd, hh⟩ := hfacts p hp
    have he' := match2_sound ff Sig.cst (sigWord r t)
      (fun a w ha => by cases a <;> simp [Sig.cst] at ha; subst ha; rfl)
      (fun k a hk => slotSig_sound hb hz hdi hk) (fun k a hk => slotSig_sound hb hz hd hk) _ _ hm
    simp only [ctxEnv, Nat.sub_zero] at he'
    simp only [Expr.holds, he']
    exact hh
  · cases hpe : parseAtom e with
    | none => simp [hpe] at hatom
    | some at_ =>
      cases hra : resolveAtom s z (.kid i 0) at_ with
      | none => simp [hpe, hra] at hatom
      | some g =>
        simp only [hpe, hra, Option.bind_some, Bool.or_eq_true] at hatom
        have hg : g.sem r t := by
          rcases hatom with hc | hp
          · exact constHolds_sound ff hc
          · exact proveAtom_sound ff hatoms hp
        have := (resolveAtom_sound ff hb hz hdi hpe hra).mpr hg
        simpa [ctxEnv] using this

/-! ### Guards and constant Booleans -/

/-- The Boolean signal `b` of a guard `¬b`. -/
def guardSig (s : CSys) (z : Bool) (ctx : Ctx) : Expr → Option Sig
  | .not (.ref _ k .bool) => slotSig s z ctx k
  | _ => none

/-- The value of a formula made only of Boolean literals and Boolean fields that the wires
feed constants. -/
def boolConst (s : CSys) (z : Bool) (ctx : Ctx) : Expr → Option Bool
  | .blit b => some b
  | .ref _ k .bool => match slotSig s z ctx k with
    | some (.const w) => some (w != 0)
    | _ => none
  | .not a => (boolConst s z ctx a).map (!·)
  | .and a b => match boolConst s z ctx a, boolConst s z ctx b with
    | some x, some y => some (x && y)
    | _, _ => none
  | .or a b => match boolConst s z ctx a, boolConst s z ctx b with
    | some x, some y => some (x || y)
    | _, _ => none
  | _ => none

/-- The facts, and the bodies of guarded facts `¬b ∨ body` whose guard signal `b` is assumed
true (in `G`). -/
def expandFacts (s : CSys) (z : Bool) (G : List Sig) (facts : List (Ctx × Expr)) :
    List (Ctx × Expr) :=
  facts ++ facts.flatMap fun p => match p.2 with
    | .or a b => match guardSig s z p.1 a with
      | some sg => if decide (sg ∈ G) then b.conjuncts.map fun e => (p.1, e) else []
      | none => []
    | _ => []

/-- The obligation follows from the facts: as a leaf (`conjunctOK`), as a constant Boolean, or
by its structure: both sides of a conjunction; one side of a disjunction; or, for a guarded
disjunction `¬b ∨ body`, the body with `b` assumed true (the guarded facts with the same guard
then give their bodies). `G`: the guard signals assumed true. -/
def goalOK (s : CSys) (z : Bool) (i : Nat) (facts : List (Ctx × Expr)) :
    Nat → List Sig → Expr → Bool
  | 0, _, _ => false
  | n + 1, G, e =>
    conjunctOK s z i (expandFacts s z G facts) e ||
    decide (boolConst s z (.kid i 0) e = some true) ||
    match e with
    | .and a b => goalOK s z i facts n G a && goalOK s z i facts n G b
    | .or a b => goalOK s z i facts n G a || goalOK s z i facts n G b ||
        (match guardSig s z (.kid i 0) a with
         | some sg => goalOK s z i facts n (sg :: G) b
         | none => false)
    | _ => false

theorem holds_or {env : Array UInt32} {a b : Expr} :
    Expr.holds env (.or a b) = (Expr.holds env a || Expr.holds env b) := rfl

theorem holds_and {env : Array UInt32} {a b : Expr} :
    Expr.holds env (.and a b) = (Expr.holds env a && Expr.holds env b) := rfl

theorem guardSig_sound {exe : Checked → Trace → Prop} {s : CSys} {r : Run}
    (hb : Beh exe (.system s) r) {z : Bool} {t : Nat} (hz : z = true ↔ t = 0) {ctx : Ctx}
    (hd : ∀ j d, ctx = .kid j d → d ≤ t) {a : Expr} {sg : Sig}
    (h : guardSig s z ctx a = some sg) :
    Expr.holds (ctxEnv r t ctx) a = !(sigWord r t sg != 0) := by
  unfold guardSig at h
  split at h
  · rename_i n k
    rw [← slotSig_sound hb hz hd h]
    rfl
  · cases h

theorem boolConst_sound {exe : Checked → Trace → Prop} {s : CSys} {r : Run}
    (hb : Beh exe (.system s) r) {z : Bool} {t : Nat} (hz : z = true ↔ t = 0) {ctx : Ctx}
    (hd : ∀ j d, ctx = .kid j d → d ≤ t) :
    ∀ (e : Expr) (v : Bool), boolConst s z ctx e = some v →
      Expr.eval (ctxEnv r t ctx) e = .bool v := by
  intro e
  induction e with
  | blit b => intro v h; simp [boolConst] at h; subst h; rfl
  | ref n k ty =>
    intro v h
    cases ty with
    | bool =>
      simp only [boolConst] at h
      split at h
      · rename_i w hw
        cases h
        rw [eval_ref, ite_eq_left rfl, slotSig_sound hb hz hd hw]
        rfl
      · cases h
    | _ => simp [boolConst] at h
  | not a iha =>
    intro v h
    simp only [boolConst] at h
    cases ha : boolConst s z ctx a with
    | none => simp [ha] at h
    | some x =>
      have hx : v = !x := by simp [ha] at h; rw [h]; simp
      subst hx
      simp only [Expr.eval, iha x ha, Expr.Val.toBool]
  | and a b iha ihb | or a b iha ihb =>
    intro v h
    simp only [boolConst] at h
    cases ha : boolConst s z ctx a with
    | none => simp [ha] at h
    | some x =>
      cases hb' : boolConst s z ctx b with
      | none => simp [ha, hb'] at h
      | some y =>
        simp [ha, hb'] at h
        subst h
        simp only [Expr.eval, iha x ha, ihb y hb', Expr.Val.toBool]
  | _ => intro v h; simp [boolConst] at h

theorem expandFacts_hold {exe : Checked → Trace → Prop} {s : CSys} {r : Run}
    (hb : Beh exe (.system s) r) {z : Bool} {t : Nat} (hz : z = true ↔ t = 0)
    {G : List Sig} (hG : ∀ sg, sg ∈ G → sigWord r t sg ≠ 0) {facts : List (Ctx × Expr)}
    (hf : FactsHold r t facts) : FactsHold r t (expandFacts s z G facts) := by
  intro p hp
  simp only [expandFacts, List.mem_append, List.mem_flatMap] at hp
  rcases hp with hp | ⟨q, hq, hpq⟩
  · exact hf p hp
  · obtain ⟨hd, hh⟩ := hf q hq
    generalize hq2 : q.2 = e at hpq hh
    cases e with
    | or a b =>
      simp only at hpq
      cases hg : guardSig s z q.1 a with
      | none => simp [hg] at hpq
      | some sg =>
        simp only [hg] at hpq
        split at hpq
        · rename_i hmem
          simp only [List.mem_map] at hpq
          obtain ⟨e, he, rfl⟩ := hpq
          refine ⟨hd, ?_⟩
          have hga := guardSig_sound hb hz hd hg
          have hw := hG sg (by simpa using hmem)
          rw [holds_or, hga] at hh
          have : (sigWord r t sg != 0) = true := by simpa using hw
          rw [this] at hh
          simp only [Bool.not_true, Bool.false_or] at hh
          exact conjuncts_holds _ hh e he
        · simp at hpq
    | _ => simp at hpq

theorem goalOK_sound (ff : FloatFacts) {exe : Checked → Trace → Prop} {s : CSys} {r : Run}
    (hb : Beh exe (.system s) r) {z : Bool} {t : Nat} (hz : z = true ↔ t = 0) {i : Nat}
    {facts : List (Ctx × Expr)} (hf : FactsHold r t facts) :
    ∀ (n : Nat) (G : List Sig) (e : Expr), (∀ sg, sg ∈ G → sigWord r t sg ≠ 0) →
      goalOK s z i facts n G e = true → Expr.holds ((r.kid i).root.env t) e = true := by
  intro n
  induction n with
  | zero => intro G e _ h; simp [goalOK] at h
  | succ n ih =>
    intro G e hG h
    have hdi : ∀ j d, Ctx.kid i 0 = .kid j d → d ≤ t := fun _ _ h => by cases h; omega
    simp only [goalOK, Bool.or_eq_true] at h
    rcases h with ⟨hleaf | hconst⟩ | hstruct
    · exact conjunctOK_sound ff hb hz (expandFacts_hold hb hz hG hf) hleaf
    · have := boolConst_sound hb hz hdi e true (by simpa using hconst)
      simp only [ctxEnv, Nat.sub_zero] at this
      simp only [Expr.holds, this, Expr.Val.toBool]
    · cases e with
      | and a b =>
        simp only [Bool.and_eq_true] at hstruct
        rw [holds_and, ih G a hG hstruct.1, ih G b hG hstruct.2]; rfl
      | or a b =>
        simp only [Bool.or_eq_true] at hstruct
        rw [holds_or]
        rcases hstruct with ⟨ha | hb'⟩ | hg
        · rw [ih G a hG ha]; rfl
        · rw [ih G b hG hb']; simp
        · cases hgs : guardSig s z (.kid i 0) a with
          | none => simp [hgs] at hg
          | some sg =>
            simp only [hgs] at hg
            have hga := guardSig_sound hb hz hdi hgs
            simp only [ctxEnv, Nat.sub_zero] at hga
            rw [hga]
            by_cases hw : sigWord r t sg = 0
            · simp [hw]
            · have hG' : ∀ sg', sg' ∈ sg :: G → sigWord r t sg' ≠ 0 := by
                intro sg' hm
                simp only [List.mem_cons] at hm
                rcases hm with rfl | hm
                · exact hw
                · exact hG sg' hm
              rw [ih (sg :: G) b hG' hg]; simp
      | _ => simp at hstruct

/-- The fuel of `goalOK`: deeper than any formula the checker is given. -/
def goalFuel : Nat := 1000

/-- The range checker: in both cases of the first tick, assumption clause `k` of child `i`
follows from the cited clauses (`goalOK`). -/
def rangeCheck (s : CSys) (i k : Nat) (cs : List Cite) : Bool :=
  [true, false].all fun z =>
    goalOK s z i (citedFacts s z cs) goalFuel [] ((child s i).view.assume[k]!).expr

theorem rangeCheck_sound (ff : FloatFacts) {exe : Checked → Trace → Prop} {s : CSys}
    {i k : Nat} {cs : List Cite} (h : rangeCheck s i k cs = true) :
    CitedDis exe s i k cs := by
  intro r hb t hav
  let z := decide (t = 0)
  have hz : z = true ↔ t = 0 := by simp [z]
  have hcase : goalOK s z i (citedFacts s z cs) goalFuel [] ((child s i).view.assume[k]!).expr
      = true := by
    simp only [rangeCheck, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true] at h
    by_cases h0 : t = 0 <;> simp [z, h0, h.1, h.2]
  -- every usable cited conjunct holds in its environment
  have hfacts : FactsHold r t (citedFacts s z cs) := by
    intro p hp
    simp only [citedFacts, List.mem_flatMap] at hp
    obtain ⟨c, hc, hpc⟩ := hp
    have hac := hav c hc
    cases c with
    | assume q =>
      simp only [List.mem_map] at hpc
      obtain ⟨e, he, rfl⟩ := hpc
      exact ⟨fun _ _ h => (by cases h), conjuncts_holds _ hac e he⟩
    | guar j p' k' lag =>
      cases p' with
      | cons _ _ => simp at hpc
      | nil =>
        simp only at hpc
        split at hpc
        · rename_i hcond
          simp only [List.mem_map] at hpc
          obtain ⟨e, he, rfl⟩ := hpc
          have hlag : lag ≤ t := by
            simp only [Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq,
              Bool.not_eq_true'] at hcond
            rcases hcond.2 with ⟨hz1, hl⟩ | ⟨hz0, hl⟩
            · omega
            · have : t ≠ 0 := fun h0 => by simp [z, h0] at hz0
              omega
          refine ⟨fun j' d h => by cases h; exact hlag, ?_⟩
          exact conjuncts_holds _ (hac hlag) e he
        · simp at hpc
  exact goalOK_sound ff hb hz hfacts goalFuel [] _ (fun _ h => by cases h) hcase

end Harness.Link
