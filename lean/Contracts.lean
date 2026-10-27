/-!
# Assume–guarantee contracts over sets of behaviours

Everything here is stated over an arbitrary type `B` of behaviours (for instance, trajectories of the
system variables).  A property, a component, an assumption and a guarantee are all sets of behaviours,
represented as predicates `B → Prop`.  No library beyond core Lean is used.

Contracts are unsaturated pairs `(A, G)`; no operation on contracts (composition, quotient) is defined.
Every rule targets implementations: it says what a component `M`, a sequential pair `M₁ ⊗ M₂` or a parallel
pair `M₁ ∥ M₂`, satisfies.
The file defines contracts, implementation and refinement; proves the simplified refinement lemma; states
and proves the four inference rules (Refinement, Composition, Assumption Relaxation, Guarantee
Tightening); and ends with the two-component delegation theorem, derived from the rules alone.
-/

namespace AG

/-- A set of behaviours, as a predicate. -/
abbrev Behaviours (B : Type) := B → Prop

variable {B : Type}

instance : HasSubset (Behaviours B) := ⟨fun P Q => ∀ x, P x → Q x⟩
instance : Inter (Behaviours B) := ⟨fun P Q x => P x ∧ Q x⟩
instance : Union (Behaviours B) := ⟨fun P Q x => P x ∨ Q x⟩

/-- Complement, `¬A := B ∖ A`. -/
def compl (P : Behaviours B) : Behaviours B := fun x => ¬ P x

prefix:max "∁" => compl

theorem subset_def {P Q : Behaviours B} : P ⊆ Q ↔ ∀ x, P x → Q x := Iff.rfl
theorem inter_def {P Q : Behaviours B} {x : B} : (P ∩ Q) x ↔ P x ∧ Q x := Iff.rfl
theorem union_def {P Q : Behaviours B} {x : B} : (P ∪ Q) x ↔ P x ∨ Q x := Iff.rfl
theorem compl_def {P : Behaviours B} {x : B} : (∁ P) x ↔ ¬ P x := Iff.rfl

/-- An assume–guarantee contract: assumptions `A` and guarantees `G`. -/
structure Contract (B : Type) where
  A : Behaviours B
  G : Behaviours B

/-- A component `M` satisfies a property `P` when `M ⊆ P`. -/
def Satisfies (M P : Behaviours B) : Prop := M ⊆ P

/-- `M` implements `(A, G)`: for every environment `E ⊆ A`, `M ∩ E ⊆ G`. -/
def Implements (M : Behaviours B) (C : Contract B) : Prop :=
  ∀ E : Behaviours B, E ⊆ C.A → M ∩ E ⊆ C.G

/-- Notation `M ⊨ C` for `Implements M C`. -/
infix:50 " ⊨ " => Implements

/-- Implementation is the same as the single inclusion `M ∩ A ⊆ G`. -/
theorem implements_iff {M : Behaviours B} {C : Contract B} : M ⊨ C ↔ M ∩ C.A ⊆ C.G := by
  constructor
  · intro h
    exact h C.A (fun _ hx => hx)
  · intro h E hE x hx
    exact h x ⟨hx.1, hE x hx.2⟩

/-- Refinement `C₁ ⪯ C₂`: `A₂ ⊆ A₁` and `G₁ ∪ ∁A₁ ⊆ G₂ ∪ ∁A₂`. -/
def Refines (C₁ C₂ : Contract B) : Prop :=
  C₂.A ⊆ C₁.A ∧ (C₁.G ∪ ∁ C₁.A) ⊆ (C₂.G ∪ ∁ C₂.A)

infix:50 " ⪯ " => Refines

/-- Pure sequential composition, `M₁ ⊗ M₂`: defined when every output of `M₁` is consumed as an input of `M₂`
and nothing flows back (an architectural condition, not tracked here). As a set of behaviours it is `M₁ ∩ M₂`. -/
def seq (M₁ M₂ : Behaviours B) : Behaviours B := M₁ ∩ M₂

infixl:70 " ⊗ " => seq

/-- Pure parallel composition, `M₁ ∥ M₂`: defined when no wire joins the two (shared inputs allowed). As a set
of behaviours it is `M₁ ∩ M₂`. -/
def par (M₁ M₂ : Behaviours B) : Behaviours B := M₁ ∩ M₂

infixl:70 " ∥ " => par

/-- The triangle `Tria M₁ M₂ M₃`: wires `M₁ → M₂`, `M₁ → M₃`, `M₂ → M₃`. `M₂` reads only `M₁`; `M₃` reads
`M₁` and `M₂`. Neither `⊗` nor `∥` names this shape. As a set of behaviours it is `M₁ ∩ M₂ ∩ M₃`. -/
def Tria (M₁ M₂ M₃ : Behaviours B) : Behaviours B := M₁ ∩ M₂ ∩ M₃

/-- Both pure compositions are the intersection; the architecture decides which symbol is defined. -/
theorem seq_eq_par (M₁ M₂ : Behaviours B) : M₁ ⊗ M₂ = M₁ ∥ M₂ := rfl

/-- The triangle is the intersection as well: left-nested sequential, with `M₃` reading the pair. -/
theorem tria_eq_seq (M₁ M₂ M₃ : Behaviours B) : Tria M₁ M₂ M₃ = M₁ ⊗ M₂ ⊗ M₃ := rfl

/-! ## The simplified refinement lemma

Refinement is equivalent to `A₂ ⊆ A₁` and `G₁ ∩ A₂ ⊆ G₂`.  The hypothesis "`A₂` nonempty" of the informal
statement is not needed: `A₂ ⊆ A₁` already makes `∁A₁ ∩ A₂` empty. -/

theorem refines_iff {C₁ C₂ : Contract B} :
    C₁ ⪯ C₂ ↔ C₂.A ⊆ C₁.A ∧ (C₁.G ∩ C₂.A) ⊆ C₂.G := by
  constructor
  · rintro ⟨hA, hG⟩
    refine ⟨hA, fun x hx => ?_⟩
    rcases hG x (Or.inl hx.1) with h | h
    · exact h
    · exact absurd hx.2 h
  · rintro ⟨hA, hG⟩
    refine ⟨hA, fun x hx => ?_⟩
    rcases hx with h | h
    · by_cases h₂ : C₂.A x
      · exact Or.inl (hG x ⟨h, h₂⟩)
      · exact Or.inr h₂
    · exact Or.inr (fun h₂ => h (hA x h₂))

/-! ## The four inference rules -/

/-- (Refinement) `M ⊨ C₁` and `C₁ ⪯ C₂` give `M ⊨ C₂`. -/
theorem rule_refinement {M : Behaviours B} {C₁ C₂ : Contract B}
    (hM : M ⊨ C₁) (hR : C₁ ⪯ C₂) : M ⊨ C₂ := by
  rw [implements_iff] at hM ⊢
  obtain ⟨hA, hG⟩ := refines_iff.mp hR
  intro x hx
  exact hG x ⟨hM x ⟨hx.1, hA x hx.2⟩, hx.2⟩

/-- (Sequential) `M₁ ⊨ (A₁, G₁)`, `M₂ ⊨ (A₂, G₂)` and `G₁ ⊆ A₂` give `M₁ ⊗ M₂ ⊨ (A₁, G₂)`. Defined when all
outputs of `M₁` are consumed by `M₂`. -/
theorem rule_composition {M₁ M₂ A₁ G₁ A₂ G₂ : Behaviours B}
    (h₁ : M₁ ⊨ ⟨A₁, G₁⟩) (h₂ : M₂ ⊨ ⟨A₂, G₂⟩) (hG : G₁ ⊆ A₂) : M₁ ⊗ M₂ ⊨ ⟨A₁, G₂⟩ := by
  intro E hE x hx
  exact h₂ (M₁ ∩ E) (fun y hy => hG y (h₁ E hE y hy)) x ⟨hx.1.2, hx.1.1, hx.2⟩

/-- (Assumption Relaxation) `M ⊨ (A₁, G)` and `A₂ ⊆ A₁` give `M ⊨ (A₂, G)`. -/
theorem rule_assumption_relaxation {M A₁ A₂ G : Behaviours B}
    (hM : M ⊨ ⟨A₁, G⟩) (hA : A₂ ⊆ A₁) : M ⊨ ⟨A₂, G⟩ := by
  intro E hE
  exact hM E (fun x hx => hA x (hE x hx))

/-- (Guarantee Tightening) `M ⊨ (A, G₁)` and `G₁ ∩ A ⊆ G₂` give `M ⊨ (A, G₂)`. -/
theorem rule_guarantee_tightening {M A G₁ G₂ : Behaviours B}
    (hM : M ⊨ ⟨A, G₁⟩) (hG : (G₁ ∩ A) ⊆ G₂) : M ⊨ ⟨A, G₂⟩ := by
  intro E hE x hx
  exact hG x ⟨hM E hE x hx, hE x hx.2⟩

/-- (Parallel) `M₁ ⊨ (A₁, G₁)` and `M₂ ⊨ (A₂, G₂)` give `M₁ ∥ M₂ ⊨ (A₁ ∩ A₂, G₁ ∩ G₂)`. No edge condition:
the two run side by side. -/
theorem rule_parallel {M₁ M₂ A₁ G₁ A₂ G₂ : Behaviours B}
    (h₁ : M₁ ⊨ ⟨A₁, G₁⟩) (h₂ : M₂ ⊨ ⟨A₂, G₂⟩) : M₁ ∥ M₂ ⊨ ⟨A₁ ∩ A₂, G₁ ∩ G₂⟩ := by
  intro E hE x hx
  exact ⟨h₁ E (fun y hy => (hE y hy).1) x ⟨hx.1.1, hx.2⟩, h₂ E (fun y hy => (hE y hy).2) x ⟨hx.1.2, hx.2⟩⟩

/-- (Fan-in) two branches feed a third component: `G₁ ∩ G₂ ⊆ A₃` gives `(M₁ ∥ M₂) ⊗ M₃ ⊨ (A₁ ∩ A₂, G₃)`.
Derived: Parallel, then Composition. -/
theorem rule_fan_in {M₁ M₂ M₃ A₁ G₁ A₂ G₂ A₃ G₃ : Behaviours B}
    (h₁ : M₁ ⊨ ⟨A₁, G₁⟩) (h₂ : M₂ ⊨ ⟨A₂, G₂⟩) (h₃ : M₃ ⊨ ⟨A₃, G₃⟩) (hG : (G₁ ∩ G₂) ⊆ A₃) :
    (M₁ ∥ M₂) ⊗ M₃ ⊨ ⟨A₁ ∩ A₂, G₃⟩ :=
  rule_composition (rule_parallel h₁ h₂) h₃ hG

/-- (Fan-out) one component feeds two: `G₁ ⊆ A₂ ∩ A₃` gives `M₁ ⊗ (M₂ ∥ M₃) ⊨ (A₁, G₂ ∩ G₃)`.
Derived: Parallel, then Composition. -/
theorem rule_fan_out {M₁ M₂ M₃ A₁ G₁ A₂ G₂ A₃ G₃ : Behaviours B}
    (h₁ : M₁ ⊨ ⟨A₁, G₁⟩) (h₂ : M₂ ⊨ ⟨A₂, G₂⟩) (h₃ : M₃ ⊨ ⟨A₃, G₃⟩) (hG : G₁ ⊆ (A₂ ∩ A₃)) :
    M₁ ⊗ (M₂ ∥ M₃) ⊨ ⟨A₁, G₂ ∩ G₃⟩ :=
  rule_composition h₁ (rule_parallel h₂ h₃) hG

/-- (Assumption Discharge) `M ⊨ (A ∩ A', G)` and `M ∩ A ⊆ A'` give `M ⊨ (A, G)`: a conjunct of the assumption
that the component itself establishes under the rest can be dropped. -/
theorem rule_assumption_discharge {M A A' G : Behaviours B}
    (hM : M ⊨ ⟨A ∩ A', G⟩) (hA : (M ∩ A) ⊆ A') : M ⊨ ⟨A, G⟩ := by
  rw [implements_iff] at hM ⊢
  intro x hx
  exact hM x ⟨hx.1, hx.2, hA x hx⟩

/-- (Sequential) derived from Parallel, Discharge and Tightening, for unsaturated contracts:
`G₁ ⊆ A₂` gives `M₁ ⊗ M₂ ⊨ (A₁, G₂)`. -/
theorem rule_sequential {M₁ M₂ A₁ G₁ A₂ G₂ : Behaviours B}
    (h₁ : M₁ ⊨ ⟨A₁, G₁⟩) (h₂ : M₂ ⊨ ⟨A₂, G₂⟩) (hG : G₁ ⊆ A₂) : M₁ ⊗ M₂ ⊨ ⟨A₁, G₂⟩ := by
  have hp := rule_parallel h₁ h₂
  have hd : M₁ ⊗ M₂ ⊨ ⟨A₁, G₁ ∩ G₂⟩ := by
    refine rule_assumption_discharge hp (fun x hx => hG x ?_)
    exact (implements_iff.mp h₁) x ⟨hx.1.1, hx.2⟩
  exact rule_guarantee_tightening hd (fun _ hx => hx.1.2)

/-- (Mixed) `M₂` reads outputs of `M₁` and environment variables: `E ∩ G₁ ⊆ A₂` gives
`M₁ ⊗ M₂ ⊨ (E ∩ A₁, G₂)` (the second also reads environment variables: not a pure composition; kept as a
derived rule). Parallel, Relaxation, Discharge, Tightening. -/
theorem rule_mixed {M₁ M₂ E A₁ G₁ A₂ G₂ : Behaviours B}
    (h₁ : M₁ ⊨ ⟨A₁, G₁⟩) (h₂ : M₂ ⊨ ⟨A₂, G₂⟩) (hG : (E ∩ G₁) ⊆ A₂) : M₁ ⊗ M₂ ⊨ ⟨E ∩ A₁, G₂⟩ := by
  have hp := rule_parallel h₁ h₂
  have hr : M₁ ⊗ M₂ ⊨ ⟨(E ∩ A₁) ∩ A₂, G₁ ∩ G₂⟩ :=
    rule_assumption_relaxation hp (fun _ hx => ⟨hx.1.2, hx.2⟩)
  have hd : M₁ ⊗ M₂ ⊨ ⟨E ∩ A₁, G₁ ∩ G₂⟩ := by
    refine rule_assumption_discharge hr (fun x hx => hG x ⟨hx.2.1, ?_⟩)
    exact (implements_iff.mp h₁) x ⟨hx.1.1, hx.2.2⟩
  exact rule_guarantee_tightening hd (fun _ hx => hx.1.2)

/-! ## The general composition rule for unsaturated contracts

The composite's assumption `A` is a parameter. Two side conditions: `A` establishes the first assumption
outright (nothing flows back into `M₁`), and `A` together with the first guarantee establishes the second
assumption. Parallel is the instance `A := A₁ ∩ A₂`, Sequential the instance `A := A₁` when `G₁ ⊆ A₂`,
Mixed the instance `A := E ∩ A₁` when `E ∩ G₁ ⊆ A₂`. The weakest admissible `A` is `A₁ ∩ (A₂ ∪ ∁G₁)`. -/

/-- (General) `A ⊆ A₁` and `A ∩ G₁ ⊆ A₂` give `M₁ ⊗ M₂ ⊨ (A, G₁ ∩ G₂)`: the sequential rule with the
composite's assumption as a parameter (used for the chain and DAG theorems). -/
theorem rule_general {M₁ M₂ A A₁ G₁ A₂ G₂ : Behaviours B}
    (h₁ : M₁ ⊨ ⟨A₁, G₁⟩) (h₂ : M₂ ⊨ ⟨A₂, G₂⟩) (hA₁ : A ⊆ A₁) (hA₂ : (A ∩ G₁) ⊆ A₂) :
    M₁ ⊗ M₂ ⊨ ⟨A, G₁ ∩ G₂⟩ := by
  rw [implements_iff] at h₁ h₂ ⊢
  intro x hx
  have g₁ : G₁ x := h₁ x ⟨hx.1.1, hA₁ x hx.2⟩
  exact ⟨g₁, h₂ x ⟨hx.1.2, hA₂ x ⟨hx.2, g₁⟩⟩⟩

/-- Parallel is the instance `A := A₁ ∩ A₂` (same set, `seq_eq_par`). -/
theorem rule_parallel_of_general' {M₁ M₂ A₁ G₁ A₂ G₂ : Behaviours B}
    (h₁ : M₁ ⊨ ⟨A₁, G₁⟩) (h₂ : M₂ ⊨ ⟨A₂, G₂⟩) : M₁ ⊗ M₂ ⊨ ⟨A₁ ∩ A₂, G₁ ∩ G₂⟩ :=
  rule_general h₁ h₂ (fun _ hx => hx.1) (fun _ hx => hx.1.2)

/-- Sequential is the instance `A := A₁` under `G₁ ⊆ A₂`, then Tightening. -/
theorem rule_sequential_of_general {M₁ M₂ A₁ G₁ A₂ G₂ : Behaviours B}
    (h₁ : M₁ ⊨ ⟨A₁, G₁⟩) (h₂ : M₂ ⊨ ⟨A₂, G₂⟩) (hG : G₁ ⊆ A₂) : M₁ ⊗ M₂ ⊨ ⟨A₁, G₂⟩ :=
  rule_guarantee_tightening (rule_general h₁ h₂ (fun _ hx => hx) (fun x hx => hG x hx.2)) (fun _ hx => hx.1.2)

/-- Mixed is the instance `A := E ∩ A₁` under `E ∩ G₁ ⊆ A₂`, then Tightening. -/
theorem rule_mixed_of_general' {M₁ M₂ E A₁ G₁ A₂ G₂ : Behaviours B}
    (h₁ : M₁ ⊨ ⟨A₁, G₁⟩) (h₂ : M₂ ⊨ ⟨A₂, G₂⟩) (hG : (E ∩ G₁) ⊆ A₂) : M₁ ⊗ M₂ ⊨ ⟨E ∩ A₁, G₂⟩ :=
  rule_guarantee_tightening (rule_general h₁ h₂ (fun _ hx => hx.2) (fun x hx => hG x ⟨hx.1.1, hx.2⟩))
    (fun _ hx => hx.1.2)

/-- The weakest admissible assumption: `A` satisfies both side conditions iff `A ⊆ A₁ ∩ (A₂ ∪ ∁G₁)`. -/
theorem general_assumption_iff {A A₁ G₁ A₂ : Behaviours B} :
    (A ⊆ A₁ ∧ (A ∩ G₁) ⊆ A₂) ↔ A ⊆ (A₁ ∩ (A₂ ∪ ∁ G₁)) := by
  constructor
  · rintro ⟨h₁, h₂⟩ x hx
    refine ⟨h₁ x hx, ?_⟩
    by_cases hg : G₁ x
    · exact Or.inl (h₂ x ⟨hx, hg⟩)
    · exact Or.inr hg
  · intro h
    refine ⟨fun x hx => (h x hx).1, fun x hx => ?_⟩
    rcases (h x hx.1).2 with h' | h'
    · exact h'
    · exact absurd hx.2 h'

/-- (Triangle) From `M_i ⊨ (A_i, G_i)`, `G₁ ⊆ A₂` and `G₁ ∩ G₂ ⊆ A₃`: `Tria M₁ M₂ M₃ ⊨ (A₁, G₃)`.
`M₂`'s assumption is established by its one writer; `M₃`'s by both of its writers together. -/
theorem rule_triangle {M₁ M₂ M₃ A₁ G₁ A₂ G₂ A₃ G₃ : Behaviours B}
    (h₁ : M₁ ⊨ ⟨A₁, G₁⟩) (h₂ : M₂ ⊨ ⟨A₂, G₂⟩) (h₃ : M₃ ⊨ ⟨A₃, G₃⟩)
    (e₁ : G₁ ⊆ A₂) (e₂ : (G₁ ∩ G₂) ⊆ A₃) :
    Tria M₁ M₂ M₃ ⊨ ⟨A₁, G₃⟩ := by
  rw [implements_iff] at h₁ h₂ h₃ ⊢
  intro x hx
  -- hx : x ∈ M₁ ∩ M₂ ∩ M₃ and x ∈ A₁
  have g₁ : G₁ x := h₁ x ⟨hx.1.1.1, hx.2⟩
  have g₂ : G₂ x := h₂ x ⟨hx.1.1.2, e₁ x g₁⟩
  exact h₃ x ⟨hx.1.2, e₂ x ⟨g₁, g₂⟩⟩

/-- The same rule derived from the guarantee-keeping Sequential rule applied twice, instead of pointwise:
`(M₁ ⊗ M₂) ⊨ (A₁, G₁ ∩ G₂)` by `rule_general`, then `rule_composition` with `G₁ ∩ G₂ ⊆ A₃`. -/
theorem rule_triangle_of_sequential {M₁ M₂ M₃ A₁ G₁ A₂ G₂ A₃ G₃ : Behaviours B}
    (h₁ : M₁ ⊨ ⟨A₁, G₁⟩) (h₂ : M₂ ⊨ ⟨A₂, G₂⟩) (h₃ : M₃ ⊨ ⟨A₃, G₃⟩)
    (e₁ : G₁ ⊆ A₂) (e₂ : (G₁ ∩ G₂) ⊆ A₃) :
    Tria M₁ M₂ M₃ ⊨ ⟨A₁, G₃⟩ := by
  have h₁₂ : M₁ ⊗ M₂ ⊨ ⟨A₁, G₁ ∩ G₂⟩ :=
    rule_general h₁ h₂ (fun _ hx => hx) (fun _ hx => e₁ _ hx.2)
  rw [tria_eq_seq]
  exact rule_composition h₁₂ h₃ e₂

/-! ## The two-component delegation theorem

Given a top-level contract `(A, G)` and components `M₁ ⊗ M₂`, choose `A₁ ⊇ A`, `G₁ ⊆ A₂`, and `G₂` with
`G₂ ∩ A₂ ⊆ G`.  If `M₁ ⊨ (A₁, G₁)` and `M₂ ⊨ (A₂, G₂)`, then `M₁ ⊗ M₂ ⊨ (A, G)`.

The proof uses the rules only, in this order: Guarantee Tightening on `M₂` (to `(A₂, G)`), Composition
(to `(A₁, G)`), Assumption Relaxation (to `(A, G)`).  Note that tightening is applied before composing:
after composing, the available fact `G₂ ∩ A₂ ⊆ G` is not of the form the tightening rule needs. -/

theorem delegation
    {M₁ M₂ A G A₁ G₁ A₂ G₂ : Behaviours B}
    (hA : A ⊆ A₁) (hG₁ : G₁ ⊆ A₂)
    (hG₂ : (G₂ ∩ A₂) ⊆ G)
    (hM₁ : M₁ ⊨ ⟨A₁, G₁⟩) (hM₂ : M₂ ⊨ ⟨A₂, G₂⟩) :
    M₁ ⊗ M₂ ⊨ ⟨A, G⟩ := by
  have h₂ : M₂ ⊨ ⟨A₂, G⟩ :=
    rule_guarantee_tightening hM₂ hG₂
  have h₁₂ : M₁ ⊗ M₂ ⊨ ⟨A₁, G⟩ :=
    rule_composition hM₁ h₂ hG₁
  exact rule_assumption_relaxation h₁₂ hA

end AG
