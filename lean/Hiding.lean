import Contracts
/-!
# Hiding the wires consumed inside a composition

In the architecture, an output of `M₁` consumed entirely by `M₂` is not an output wire of the box around
`M₁ ∥ M₂`. Model this by splitting behaviours into an external part `X` and a hidden part `H`:
`B = X × H`. Hiding is existential projection, `hide P = {x | ∃ h, (x, h) ∈ P}`; an external set `A ⊆ X`
is read as a cylinder `lift A` over `X × H`.

The result: if the composite implements `(lift A, G)` over all variables, then the box implements
`(A, hide G)` over the external wires. Delegation checks are unchanged, because the query's `A` and `G` are
external anyway and `hide (P) ∩ A ⊆ G` is the same as `P ∩ lift A ⊆ lift G`. The quantifier appears only when
one writes down the composite's own guarantee over its external wires.
-/

namespace AG

variable {X H : Type}

/-- Existential projection onto the external variables. -/
def hide (P : Behaviours (X × H)) : Behaviours X := fun x => ∃ h, P (x, h)

/-- An external set as a cylinder over all variables. -/
def lift (A : Behaviours X) : Behaviours (X × H) := fun p => A p.1

/-- (Hiding) `M ⊨ (lift A, G)` gives `hide M ⊨ (A, hide G)`. -/
theorem rule_hide {M G : Behaviours (X × H)} {A : Behaviours X}
    (hM : M ⊨ ⟨lift A, G⟩) : hide M ⊨ ⟨A, hide G⟩ := by
  rw [implements_iff] at hM ⊢
  intro x hx
  obtain ⟨h, hP⟩ := hx.1
  exact ⟨h, hM (x, h) ⟨hP, hx.2⟩⟩

/-- Hiding changes nothing for an external contract: the box implements `(A, G)` over the external wires
iff the full composite implements `(lift A, lift G)`. -/
theorem hide_implements_iff {M : Behaviours (X × H)} {A G : Behaviours X} :
    hide M ⊨ ⟨A, G⟩ ↔ M ⊨ ⟨lift A, lift G⟩ := by
  rw [implements_iff, implements_iff]
  constructor
  · intro hM p hp
    exact hM p.1 ⟨⟨p.2, hp.1⟩, hp.2⟩
  · intro hM x hx
    obtain ⟨h, hP⟩ := hx.1
    exact hM (x, h) ⟨hP, hx.2⟩

/-- Composition with hiding: the general rule followed by Hiding. `A` is external, the edge variables are
hidden, and the box guarantees `hide (G₁ ∩ G₂)`. -/
theorem rule_general_hide {M₁ M₂ A₁ G₁ A₂ G₂ : Behaviours (X × H)} {A : Behaviours X}
    (h₁ : M₁ ⊨ ⟨A₁, G₁⟩) (h₂ : M₂ ⊨ ⟨A₂, G₂⟩) (hA₁ : lift A ⊆ A₁) (hA₂ : (lift A ∩ G₁) ⊆ A₂) :
    hide (M₁ ⊗ M₂) ⊨ ⟨A, hide (G₁ ∩ G₂)⟩ :=
  rule_hide (rule_general h₁ h₂ hA₁ hA₂)

end AG
