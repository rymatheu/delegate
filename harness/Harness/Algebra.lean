/-! # The harness algebra

A harness is a triple: an implementation, a contract, and the evidence that the implementation
meets the contract. This file states the algebra of such triples and proves its laws.

* Sections 1 to 3 are the contract algebra over sets of behaviours (implementation, refinement,
  composition, conjunction, quotient, hiding), restated in core Lean with sets as predicates.
* Section 4 gives contracts their tick structure: a step contract, its reading over runs, and
  the loop rule that composes modules around a feedback loop.
* Section 5 is evidence: a tree whose leaves are ledger records and whose inner nodes are Lean
  proofs, read under a trust policy.
* Section 6 is the harness and its operations, each carried by a theorem of sections 1 to 4.

Core Lean only. The implementation of a C++ module is never defined here: it is a variable, the
set of runs its executable can produce, and the claim that it meets its contract is a leaf. -/

namespace Harness.Algebra

/-! ## 1. Contracts, implementation, refinement -/

/-- A contract over behaviours `B`: an assumption and a guarantee. -/
structure Contract (B : Type) where
  A : B → Prop
  G : B → Prop

variable {B B' : Type}

/-- `M` implements `C`: every behaviour of `M` that meets the assumption meets the guarantee. -/
def Implements (M : B → Prop) (C : Contract B) : Prop := ∀ b, M b → C.A b → C.G b

@[inherit_doc] infix:50 " ⊨ " => Implements

/-- The saturated guarantee: the behaviours that meet the guarantee or break the assumption. -/
def Contract.sat (C : Contract B) : B → Prop := fun b => C.A b → C.G b

theorem implements_iff_sat {M : B → Prop} {C : Contract B} : M ⊨ C ↔ ∀ b, M b → C.sat b := Iff.rfl

/-- `C₁` refines `C₂`: it assumes no more and, saturated, guarantees no less. -/
def Refines (C₁ C₂ : Contract B) : Prop :=
  (∀ b, C₂.A b → C₁.A b) ∧ (∀ b, C₁.sat b → C₂.sat b)

@[inherit_doc] infix:50 " ⪯ " => Refines

theorem refines_refl (C : Contract B) : C ⪯ C := ⟨fun _ h => h, fun _ h => h⟩

theorem refines_trans {C₁ C₂ C₃ : Contract B} (h₁₂ : C₁ ⪯ C₂) (h₂₃ : C₂ ⪯ C₃) : C₁ ⪯ C₃ :=
  ⟨fun b h => h₁₂.1 b (h₂₃.1 b h), fun b h => h₂₃.2 b (h₁₂.2 b h)⟩

/-- An implementation of a contract implements every contract it refines. -/
theorem refines_sound {M : B → Prop} {C₁ C₂ : Contract B} (h : C₁ ⪯ C₂) (hM : M ⊨ C₁) :
    M ⊨ C₂ := fun b hb hA => h.2 b (fun hA₁ => hM b hb hA₁) hA

/-- A smaller implementation meets the same contract. -/
theorem implements_mono {M M' : B → Prop} {C : Contract B} (h : ∀ b, M' b → M b) (hM : M ⊨ C) :
    M' ⊨ C := fun b hb hA => hM b (h b hb) hA

/-! ## 2. Composition, conjunction, quotient -/

/-- Composition: both saturated guarantees; both assumptions, relaxed by every behaviour on
which a saturated guarantee already fails. -/
def comp (C₁ C₂ : Contract B) : Contract B where
  A := fun b => (C₁.A b ∧ C₂.A b) ∨ ¬ (C₁.sat b ∧ C₂.sat b)
  G := fun b => C₁.sat b ∧ C₂.sat b

@[inherit_doc] infixl:70 " ⊗ " => comp

theorem sat_comp (C₁ C₂ : Contract B) (b : B) : (C₁ ⊗ C₂).sat b ↔ C₁.sat b ∧ C₂.sat b := by
  constructor
  · intro h
    exact Classical.byContradiction fun hn => hn (h (Or.inr hn))
  · intro h _
    exact h

private theorem comp_A_iff (C₁ C₂ : Contract B) (b : B) :
    (C₁ ⊗ C₂).A b ↔ (C₁.sat b ∧ C₂.sat b → C₁.A b ∧ C₂.A b) := by
  constructor
  · intro h hs
    rcases h with h | h
    · exact h
    · exact absurd hs h
  · intro h
    by_cases hs : C₁.sat b ∧ C₂.sat b
    · exact Or.inl (h hs)
    · exact Or.inr hs

/-- Implementations compose by intersection. -/
theorem compose {M₁ M₂ : B → Prop} {C₁ C₂ : Contract B} (h₁ : M₁ ⊨ C₁) (h₂ : M₂ ⊨ C₂) :
    (fun b => M₁ b ∧ M₂ b) ⊨ C₁ ⊗ C₂ :=
  fun b hb _ => ⟨fun hA => h₁ b hb.1 hA, fun hA => h₂ b hb.2 hA⟩

theorem comp_comm (C₁ C₂ : Contract B) : C₁ ⊗ C₂ ⪯ C₂ ⊗ C₁ := by
  refine ⟨fun b h => (comp_A_iff _ _ b).2 fun hs => ?_, fun b h => ?_⟩
  · have h' := (comp_A_iff _ _ b).1 h ⟨hs.2, hs.1⟩
    exact ⟨h'.2, h'.1⟩
  · have h' := (sat_comp _ _ b).1 h
    exact (sat_comp _ _ b).2 ⟨h'.2, h'.1⟩

theorem comp_assoc_left (C₁ C₂ C₃ : Contract B) : (C₁ ⊗ C₂) ⊗ C₃ ⪯ C₁ ⊗ (C₂ ⊗ C₃) := by
  refine ⟨fun b h => (comp_A_iff _ _ b).2 fun hs => ?_, fun b h => ?_⟩
  · have h₁₂ := (sat_comp _ _ b).1 hs.1
    have s₂₃ : (C₂ ⊗ C₃).sat b := (sat_comp _ _ b).2 ⟨h₁₂.2, hs.2⟩
    have h' := (comp_A_iff _ _ b).1 h ⟨h₁₂.1, s₂₃⟩
    have a₂₃ := (comp_A_iff _ _ b).1 h'.2 ⟨h₁₂.2, hs.2⟩
    exact ⟨(comp_A_iff _ _ b).2 fun _ => ⟨h'.1, a₂₃.1⟩, a₂₃.2⟩
  · have h₁ := (sat_comp _ _ b).1 h
    have h₁₂ := (sat_comp _ _ b).1 h₁.1
    exact (sat_comp _ _ b).2 ⟨h₁₂.1, (sat_comp _ _ b).2 ⟨h₁₂.2, h₁.2⟩⟩

theorem comp_assoc_right (C₁ C₂ C₃ : Contract B) : C₁ ⊗ (C₂ ⊗ C₃) ⪯ (C₁ ⊗ C₂) ⊗ C₃ := by
  refine ⟨fun b h => (comp_A_iff _ _ b).2 fun hs => ?_, fun b h => ?_⟩
  · have h₂₃ := (sat_comp _ _ b).1 hs.2
    have s₁₂ : (C₁ ⊗ C₂).sat b := (sat_comp _ _ b).2 ⟨hs.1, h₂₃.1⟩
    have h' := (comp_A_iff _ _ b).1 h ⟨s₁₂, h₂₃.2⟩
    have a₁₂ := (comp_A_iff _ _ b).1 h'.1 ⟨hs.1, h₂₃.1⟩
    exact ⟨a₁₂.1, (comp_A_iff _ _ b).2 fun _ => ⟨a₁₂.2, h'.2⟩⟩
  · have h₁ := (sat_comp _ _ b).1 h
    have h₂₃ := (sat_comp _ _ b).1 h₁.2
    exact (sat_comp _ _ b).2 ⟨(sat_comp _ _ b).2 ⟨h₁.1, h₂₃.1⟩, h₂₃.2⟩

/-- Composition is monotone: refining a part refines the whole. -/
theorem comp_mono {C₁ C₁' C₂ C₂' : Contract B} (h₁ : C₁ ⪯ C₁') (h₂ : C₂ ⪯ C₂') :
    C₁ ⊗ C₂ ⪯ C₁' ⊗ C₂' := by
  refine ⟨fun b h => (comp_A_iff _ _ b).2 fun hs => ?_, fun b h => ?_⟩
  · have h' := (comp_A_iff _ _ b).1 h ⟨h₁.2 b hs.1, h₂.2 b hs.2⟩
    exact ⟨h₁.1 b h'.1, h₂.1 b h'.2⟩
  · have hs := (sat_comp _ _ b).1 h
    exact (sat_comp _ _ b).2 ⟨h₁.2 b hs.1, h₂.2 b hs.2⟩

/-- The chain rule: the first part's guarantee may be assumed by the second. -/
theorem chain {M₁ M₂ : B → Prop} {A G₁ G : B → Prop} (h₁ : M₁ ⊨ ⟨A, G₁⟩)
    (h₂ : M₂ ⊨ ⟨fun b => A b ∧ G₁ b, G⟩) : (fun b => M₁ b ∧ M₂ b) ⊨ ⟨A, G⟩ :=
  fun b hb hA => h₂ b hb.2 ⟨hA, h₁ b hb.1 hA⟩

/-- Conjunction: two contracts on one implementation. -/
def conj (C₁ C₂ : Contract B) : Contract B where
  A := fun b => C₁.A b ∨ C₂.A b
  G := fun b => C₁.sat b ∧ C₂.sat b

theorem implements_conj {M : B → Prop} {C₁ C₂ : Contract B} :
    M ⊨ conj C₁ C₂ ↔ M ⊨ C₁ ∧ M ⊨ C₂ := by
  constructor
  · intro h
    exact ⟨fun b hb hA => (h b hb (Or.inl hA)).1 hA, fun b hb hA => (h b hb (Or.inr hA)).2 hA⟩
  · intro h b hb _
    exact ⟨fun hA => h.1 b hb hA, fun hA => h.2 b hb hA⟩

theorem conj_refines_left (C₁ C₂ : Contract B) : conj C₁ C₂ ⪯ C₁ :=
  ⟨fun _ h => Or.inl h, fun _ h hA => (h (Or.inl hA)).1 hA⟩

theorem conj_refines_right (C₁ C₂ : Contract B) : conj C₁ C₂ ⪯ C₂ :=
  ⟨fun _ h => Or.inr h, fun _ h hA => (h (Or.inr hA)).2 hA⟩

/-- Conjunction is the greatest lower bound in the refinement order. -/
theorem refines_conj {C C₁ C₂ : Contract B} (h₁ : C ⪯ C₁) (h₂ : C ⪯ C₂) : C ⪯ conj C₁ C₂ := by
  refine ⟨fun b h => ?_, fun b hs _ => ⟨h₁.2 b hs, h₂.2 b hs⟩⟩
  rcases h with h | h
  · exact h₁.1 b h
  · exact h₂.1 b h

/-- Quotient: what the missing part must satisfy, given the whole `C` and the known part `C₁`. -/
def quot (C C₁ : Contract B) : Contract B where
  A := fun b => C.A b ∧ C₁.sat b
  G := fun b => C.sat b ∧ C₁.A b

/-- The quotient is the weakest contract whose composition with `C₁` refines `C`. -/
theorem quot_adjoint {C C₁ X : Contract B} : C₁ ⊗ X ⪯ C ↔ X ⪯ quot C C₁ := by
  constructor
  · intro h
    refine ⟨fun b hq => ?_, fun b hsX hq => ?_⟩
    · have hc := (comp_A_iff _ _ b).1 (h.1 b hq.1)
      by_cases hsX : X.sat b
      · exact (hc ⟨hq.2, hsX⟩).2
      · exact Classical.byContradiction fun hn => hsX fun hxa => absurd hxa hn
    · exact ⟨h.2 b ((sat_comp _ _ b).2 ⟨hq.2, hsX⟩),
        ((comp_A_iff _ _ b).1 (h.1 b hq.1) ⟨hq.2, hsX⟩).1⟩
  · intro h
    refine ⟨fun b hCA => (comp_A_iff _ _ b).2 fun hs => ?_, fun b hs hCA => ?_⟩
    · exact ⟨(h.2 b hs.2 ⟨hCA, hs.1⟩).2, h.1 b ⟨hCA, hs.1⟩⟩
    · have hs' := (sat_comp _ _ b).1 hs
      exact (h.2 b hs'.2 ⟨hCA, hs'.1⟩).1 hCA

/-! ## 3. Hiding -/

/-- A contract on the interface `B'`, read on the full behaviours `B` through `π`. -/
def Contract.pull (π : B → B') (C : Contract B') : Contract B where
  A := fun b => C.A (π b)
  G := fun b => C.G (π b)

/-- The implementation seen through `π`: internal signals are projected away. -/
def image (π : B → B') (M : B → Prop) : B' → Prop := fun b' => ∃ b, M b ∧ π b = b'

/-- Hiding: the projected implementation meets an interface contract exactly when the full
implementation meets that contract read on the full behaviours. -/
theorem hide {π : B → B'} {M : B → Prop} {C : Contract B'} :
    M ⊨ C.pull π ↔ image π M ⊨ C := by
  constructor
  · intro h b' hb' hA
    obtain ⟨b, hb, he⟩ := hb'
    subst he
    exact h b hb hA
  · intro h b hb hA
    exact h (π b) ⟨b, hb, rfl⟩ hA

/-! ## 4. Step contracts and the loop rule -/

/-- A step contract: what a module assumes and guarantees about a run at one tick. -/
structure Step (B : Type) where
  a : B → Nat → Prop
  g : B → Nat → Prop

/-- The reading of a step contract over runs: the guarantee holds at every tick up to which the
assumption has held. All of it sits in the guarantee; the assumption over runs is trivial. -/
def Step.always (S : Step B) : Contract B where
  A := fun _ => True
  G := fun b => ∀ t, (∀ s, s ≤ t → S.a b s) → S.g b t

/-- A module that meets its step contract tick by tick meets its reading over runs. -/
theorem always_of_pointwise {M : B → Prop} {S : Step B}
    (h : ∀ b, M b → ∀ t, S.a b t → S.g b t) : M ⊨ S.always :=
  fun b hb _ t ha => h b hb t (ha t (Nat.le_refl t))

/-- The loop rule. Modules `0, …, n-1` run in this order within a tick. If each module's
assumption at tick `t` follows from the environment's assumption `e` up to `t`, the guarantees
of the modules scheduled before it at `t`, and the guarantees of all modules at earlier ticks,
then the modules together guarantee every module's guarantee for as long as `e` holds. No
assumption is discharged by a guarantee of the same tick from a module scheduled later: that is
the condition that the schedule has no instantaneous loop. -/
theorem loop (n : Nat) (M : Nat → B → Prop) (S : Nat → Step B) (e : B → Nat → Prop)
    (hM : ∀ i, i < n → M i ⊨ (S i).always)
    (hA : ∀ b t, (∀ s, s ≤ t → e b s) → ∀ i, i < n →
      (∀ j, j < i → (S j).g b t) → (∀ j, j < n → ∀ s, s < t → (S j).g b s) → (S i).a b t) :
    (fun b => ∀ i, i < n → M i b) ⊨
      (Step.mk e (fun b t => ∀ i, i < n → (S i).g b t)).always := by
  intro b hb _
  have key : ∀ t, (∀ s, s ≤ t → e b s) → ∀ i, i < n → (S i).a b t ∧ (S i).g b t := by
    intro t
    induction t using Nat.strongRecOn with
    | ind t ih =>
      intro he i
      induction i using Nat.strongRecOn with
      | ind i ihi =>
        intro hi
        have hprev : ∀ j, j < n → ∀ s, s < t → (S j).g b s := fun j hj s hs =>
          (ih s hs (fun s' hs' => he s' (Nat.le_trans hs' (Nat.le_of_lt hs))) j hj).2
        have hcur : ∀ j, j < i → (S j).g b t := fun j hj => (ihi j hj (Nat.lt_trans hj hi)).2
        have ha : (S i).a b t := hA b t he i hi hcur hprev
        refine ⟨ha, hM i hi b (hb i hi) trivial t fun s hs => ?_⟩
        rcases Nat.lt_or_eq_of_le hs with hlt | heq
        · exact (ih s hlt (fun s' hs' => he s' (Nat.le_trans hs' (Nat.le_of_lt hlt))) i hi).1
        · rw [heq]
          exact ha
  intro t he i hi
  exact (key t he i hi).2

/-- The loop rule for a plant and a controller. The controller's assumption at tick `t` follows
from the plant's guarantee at `t`; the plant's assumption at `t` follows from both guarantees
at earlier ticks. -/
theorem loop_two {Mp Mc : B → Prop} {Sp Sc : Step B} {e : B → Nat → Prop}
    (hp : Mp ⊨ Sp.always) (hc : Mc ⊨ Sc.always)
    (hAp : ∀ b t, (∀ s, s ≤ t → e b s) → (∀ s, s < t → Sp.g b s ∧ Sc.g b s) → Sp.a b t)
    (hAc : ∀ b t, (∀ s, s ≤ t → e b s) → Sp.g b t → Sc.a b t) :
    (fun b => Mp b ∧ Mc b) ⊨ (Step.mk e (fun b t => Sp.g b t ∧ Sc.g b t)).always := by
  intro b hb _
  have key : ∀ t, (∀ s, s ≤ t → e b s) → (Sp.a b t ∧ Sp.g b t) ∧ (Sc.a b t ∧ Sc.g b t) := by
    intro t
    induction t using Nat.strongRecOn with
    | ind t ih =>
      intro he
      have hr : ∀ s, s < t → ∀ s', s' ≤ s → e b s' := fun s hs s' hs' =>
        he s' (Nat.le_trans hs' (Nat.le_of_lt hs))
      have hpa : Sp.a b t :=
        hAp b t he fun s hs => ⟨(ih s hs (hr s hs)).1.2, (ih s hs (hr s hs)).2.2⟩
      have hpg : Sp.g b t := hp b hb.1 trivial t fun s hs => by
        rcases Nat.lt_or_eq_of_le hs with hlt | heq
        · exact (ih s hlt (hr s hlt)).1.1
        · rw [heq]
          exact hpa
      have hca : Sc.a b t := hAc b t he hpg
      have hcg : Sc.g b t := hc b hb.2 trivial t fun s hs => by
        rcases Nat.lt_or_eq_of_le hs with hlt | heq
        · exact (ih s hlt (hr s hlt)).2.1
        · rw [heq]
          exact hca
      exact ⟨⟨hpa, hpg⟩, ⟨hca, hcg⟩⟩
  intro t he
  exact ⟨(key t he).1.2, (key t he).2.2⟩

/-! ## 5. Evidence -/

/-- The kinds of leaf evidence a ledger holds. -/
inductive Kind where
  | proved | tested | monitored | assumed
  deriving DecidableEq, Repr

/-- Evidence for a claim `P`, with leaf records of type `ρ`.

* `leaf`: a ledger record offered for `P`. Lean cannot check it.
* `derive`: a Lean proof that the claim follows from a claim with evidence.
* `and`, `all`: evidence for each of several claims.
* `alt`: a second, independent support for the same claim. -/
inductive Ev (ρ : Type) : Prop → Type where
  | leaf (P : Prop) (r : ρ) : Ev ρ P
  | derive {P Q : Prop} (E : Ev ρ Q) (h : Q → P) : Ev ρ P
  | and {P Q : Prop} (E₁ : Ev ρ P) (E₂ : Ev ρ Q) : Ev ρ (P ∧ Q)
  | all {n : Nat} {Q : Nat → Prop} (E : (i : Fin n) → Ev ρ (Q i)) : Ev ρ (∀ i, i < n → Q i)
  | alt {P : Prop} (E₁ E₂ : Ev ρ P) : Ev ρ P

variable {ρ : Type}

/-- The evidence reaches its claim using only records the policy `T` accepts. -/
def Ev.supported (T : ρ → Prop) : {P : Prop} → Ev ρ P → Prop
  | _, .leaf _ r => T r
  | _, .derive E _ => E.supported T
  | _, .and E₁ E₂ => E₁.supported T ∧ E₂.supported T
  | _, .all E => ∀ i, (E i).supported T
  | _, .alt E₁ E₂ => E₁.supported T ∨ E₂.supported T

/-- Every record the policy `T` accepts is true of its claim. This is what trusting `T` means. -/
def Ev.faithful (T : ρ → Prop) : {P : Prop} → Ev ρ P → Prop
  | _, .leaf P r => T r → P
  | _, .derive E _ => E.faithful T
  | _, .and E₁ E₂ => E₁.faithful T ∧ E₂.faithful T
  | _, .all E => ∀ i, (E i).faithful T
  | _, .alt E₁ E₂ => E₁.faithful T ∧ E₂.faithful T

/-- Soundness of evidence: if the accepted records are true, a supported claim holds. -/
theorem Ev.sound {T : ρ → Prop} {P : Prop} (E : Ev ρ P) (hf : E.faithful T) (hs : E.supported T) :
    P := by
  induction E with
  | leaf _ _ => exact hf hs
  | derive _ h ih => exact h (ih hf hs)
  | and _ _ ih₁ ih₂ => exact ⟨ih₁ hf.1 hs.1, ih₂ hf.2 hs.2⟩
  | all _ ih => exact fun i hi => ih ⟨i, hi⟩ (hf ⟨i, hi⟩) (hs ⟨i, hi⟩)
  | alt _ _ ih₁ ih₂ =>
    rcases hs with hs | hs
    · exact ih₁ hf.1 hs
    · exact ih₂ hf.2 hs

/-- Accepting more records supports more claims. -/
theorem Ev.supported_mono {T T' : ρ → Prop} (h : ∀ r, T r → T' r) {P : Prop} (E : Ev ρ P)
    (hs : E.supported T) : E.supported T' := by
  induction E with
  | leaf _ r => exact h r hs
  | derive _ _ ih => exact ih hs
  | and _ _ ih₁ ih₂ => exact ⟨ih₁ hs.1, ih₂ hs.2⟩
  | all _ ih => exact fun i => ih i (hs i)
  | alt _ _ ih₁ ih₂ =>
    rcases hs with hs | hs
    · exact Or.inl (ih₁ hs)
    · exact Or.inr (ih₂ hs)

private theorem Ev.faithful_empty {P : Prop} (E : Ev ρ P) : E.faithful (fun _ => False) := by
  induction E with
  | leaf _ _ => exact fun h => h.elim
  | derive _ _ ih => exact ih
  | and _ _ ih₁ ih₂ => exact ⟨ih₁, ih₂⟩
  | all _ ih => exact fun i => ih i
  | alt _ _ ih₁ ih₂ => exact ⟨ih₁, ih₂⟩

/-- Evidence with no leaves that the policy needs: a claim supported under the empty policy is a
theorem. -/
theorem Ev.proved_of_supported_empty {P : Prop} (E : Ev ρ P) (hs : E.supported (fun _ => False)) :
    P := Ev.sound E (Ev.faithful_empty E) hs

/-! ## 6. Harnesses -/

/-- A harness: an implementation, a contract, and evidence that the first meets the second. -/
structure Harness (ρ : Type) (B : Type) where
  impl : B → Prop
  contract : Contract B
  ev : Ev ρ (impl ⊨ contract)

namespace Harness

/-- The claim a harness makes. -/
def Valid (H : Harness ρ B) : Prop := H.impl ⊨ H.contract

/-- The harness is backed under the policy `T`. -/
def Backed (T : ρ → Prop) (H : Harness ρ B) : Prop := H.ev.supported T

/-- The accepted records in the harness's evidence are true. -/
def Faithful (T : ρ → Prop) (H : Harness ρ B) : Prop := H.ev.faithful T

/-- Soundness: under a policy whose accepted records are true, a backed harness is valid. -/
theorem sound {T : ρ → Prop} (H : Harness ρ B) (hf : H.Faithful T) (hb : H.Backed T) : H.Valid :=
  Ev.sound H.ev hf hb

/-- A module with a ledger record. -/
def leaf (M : B → Prop) (C : Contract B) (r : ρ) : Harness ρ B := ⟨M, C, .leaf _ r⟩

/-- Compose. -/
def comp (H₁ H₂ : Harness ρ B) : Harness ρ B where
  impl := fun b => H₁.impl b ∧ H₂.impl b
  contract := H₁.contract ⊗ H₂.contract
  ev := .derive (.and H₁.ev H₂.ev) (fun h => compose h.1 h.2)

/-- Refine: the same implementation under a contract the old one refines. -/
def refine (H : Harness ρ B) (C' : Contract B) (h : H.contract ⪯ C') : Harness ρ B where
  impl := H.impl
  contract := C'
  ev := .derive H.ev (refines_sound h)

/-- Conjoin: a second contract on the same implementation, with its own evidence. -/
def conjoin (H : Harness ρ B) (C₂ : Contract B) (E₂ : Ev ρ (H.impl ⊨ C₂)) : Harness ρ B where
  impl := H.impl
  contract := conj H.contract C₂
  ev := .derive (.and H.ev E₂) (fun h => implements_conj.mpr h)

/-- A second, independent support for the same claim. -/
def support (H : Harness ρ B) (E : Ev ρ (H.impl ⊨ H.contract)) : Harness ρ B where
  impl := H.impl
  contract := H.contract
  ev := .alt H.ev E

/-- Hide: the composite seen at its interface, under an interface contract. -/
def hide (π : B → B') (H : Harness ρ B) (C' : Contract B') (h : H.contract ⪯ C'.pull π) :
    Harness ρ B' where
  impl := image π H.impl
  contract := C'
  ev := .derive H.ev (fun hM => Algebra.hide.mp (refines_sound h hM))

/-- Fill: a part `H₂` whose contract refines the quotient completes `H₁` to the whole `C`. -/
def fill (H₁ H₂ : Harness ρ B) (C : Contract B) (h : H₂.contract ⪯ quot C H₁.contract) :
    Harness ρ B where
  impl := fun b => H₁.impl b ∧ H₂.impl b
  contract := C
  ev := .derive (.and H₁.ev H₂.ev)
    (fun hh => refines_sound (quot_adjoint.mpr h) (compose hh.1 hh.2))

/-- Loop: `n` harnesses whose contracts refine step contracts, scheduled in order, closed around
a loop by the loop rule. The result is again a harness with a step contract. -/
def loop (n : Nat) (H : Nat → Harness ρ B) (S : Nat → Step B) (e : B → Nat → Prop)
    (hC : ∀ i, i < n → (H i).contract ⪯ (S i).always)
    (hA : ∀ b t, (∀ s, s ≤ t → e b s) → ∀ i, i < n →
      (∀ j, j < i → (S j).g b t) → (∀ j, j < n → ∀ s, s < t → (S j).g b s) → (S i).a b t) :
    Harness ρ B where
  impl := fun b => ∀ i, i < n → (H i).impl b
  contract := (Step.mk e (fun b t => ∀ i, i < n → (S i).g b t)).always
  ev := .derive (.all (n := n) (Q := fun i => (H i).impl ⊨ (H i).contract) (fun i => (H i).ev))
    (fun hh => Algebra.loop n (fun i => (H i).impl) S e
      (fun i hi => refines_sound (hC i hi) (hh i hi)) hA)

/-! ### Laws -/

/-- The contract of a composite is the composite of the contracts: forgetting implementation and
evidence maps the harness algebra onto the contract algebra. -/
theorem contract_comp (H₁ H₂ : Harness ρ B) : (comp H₁ H₂).contract = H₁.contract ⊗ H₂.contract :=
  rfl

/-- Swap: replacing a part by another harness with the same contract leaves the contract of the
whole unchanged. -/
theorem contract_comp_swap {H₁ H₁' : Harness ρ B} (H₂ : Harness ρ B)
    (h : H₁'.contract = H₁.contract) : (comp H₁' H₂).contract = (comp H₁ H₂).contract := by
  show H₁'.contract ⊗ H₂.contract = H₁.contract ⊗ H₂.contract
  rw [h]

/-- Refining a part refines the whole: the parent's contract need not be restated. -/
theorem contract_comp_mono {H₁ H₁' H₂ : Harness ρ B} (h : H₁'.contract ⪯ H₁.contract) :
    (comp H₁' H₂).contract ⪯ (comp H₁ H₂).contract := comp_mono h (refines_refl _)

/-- Weakest link: a composite is backed exactly when both parts are. -/
theorem backed_comp {T : ρ → Prop} (H₁ H₂ : Harness ρ B) :
    (comp H₁ H₂).Backed T ↔ H₁.Backed T ∧ H₂.Backed T := Iff.rfl

theorem backed_refine {T : ρ → Prop} (H : Harness ρ B) (C' : Contract B) (h : H.contract ⪯ C') :
    (refine H C' h).Backed T ↔ H.Backed T := Iff.rfl

theorem backed_hide {T : ρ → Prop} (π : B → B') (H : Harness ρ B) (C' : Contract B')
    (h : H.contract ⪯ C'.pull π) : (hide π H C' h).Backed T ↔ H.Backed T := Iff.rfl

/-- A second support backs the claim when either support does. -/
theorem backed_support {T : ρ → Prop} (H : Harness ρ B) (E : Ev ρ (H.impl ⊨ H.contract)) :
    (support H E).Backed T ↔ H.Backed T ∨ E.supported T := Iff.rfl

/-- A loop is backed exactly when every module in it is. -/
theorem backed_loop {T : ρ → Prop} (n : Nat) (H : Nat → Harness ρ B) (S : Nat → Step B)
    (e : B → Nat → Prop) (hC : ∀ i, i < n → (H i).contract ⪯ (S i).always)
    (hA : ∀ b t, (∀ s, s ≤ t → e b s) → ∀ i, i < n →
      (∀ j, j < i → (S j).g b t) → (∀ j, j < n → ∀ s, s < t → (S j).g b s) → (S i).a b t) :
    (loop n H S e hC hA).Backed T ↔ ∀ i : Fin n, (H i).Backed T := Iff.rfl

/-- A leaf is backed exactly when the policy accepts its record. -/
theorem backed_leaf {T : ρ → Prop} (M : B → Prop) (C : Contract B) (r : ρ) :
    (leaf M C r).Backed T ↔ T r := Iff.rfl

end Harness

end Harness.Algebra
