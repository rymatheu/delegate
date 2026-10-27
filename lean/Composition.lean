import Contracts
/-!
# Composition of contracts and the delegation scheme

`Contracts.lean` keeps to rules about implementations. This file adds the one contract-level operation the
delegation scheme is measured against: composition of contracts, which is defined for saturated contracts.
A contract `(A, G)` is saturated when `G ⊇ ∁A`; `saturate (A, G) := (A, G ∪ ∁A)` is its saturation, with the
same implementations.

The main result: under the hypotheses of the delegation scheme (`A ⊆ A₁`, `G₁ ⊆ A₂`, `G₂ ∩ A₂ ⊆ G`), the
composition of the saturated delegates refines `(A, G)`. No implementation hypothesis is needed for this.
Two further results connect it to `delegation`: implementations compose to an implementation of the
composed contract, and the Refinement rule then gives `M₁ ⊗ M₂ ⊨ (A, G)` a second way.
-/

namespace AG

variable {B : Type}

/-- Saturation: `(A, G) ↦ (A, G ∪ ∁A)`. -/
def saturate (C : Contract B) : Contract B := ⟨C.A, C.G ∪ ∁ C.A⟩

/-- Saturation does not change the implementations. -/
theorem implements_saturate {M : Behaviours B} {C : Contract B} : M ⊨ saturate C ↔ M ⊨ C := by
  rw [implements_iff, implements_iff]
  constructor
  · intro h x hx
    rcases h x hx with h' | h'
    · exact h'
    · exact absurd hx.2 h'
  · intro h x hx
    exact Or.inl (h x hx)

/-- Composition of contracts, for saturated contracts:
`(A₁, G₁) ∥ (A₂, G₂) := ((A₁ ∩ A₂) ∪ ∁(G₁ ∩ G₂), G₁ ∩ G₂)`. -/
def Contract.compose (C₁ C₂ : Contract B) : Contract B :=
  ⟨(C₁.A ∩ C₂.A) ∪ ∁ (C₁.G ∩ C₂.G), C₁.G ∩ C₂.G⟩

/-- Composition of the saturations of two unsaturated contracts. -/
def Contract.composeSat (C₁ C₂ : Contract B) : Contract B :=
  Contract.compose (saturate C₁) (saturate C₂)

/-- The delegation scheme at the level of contracts: if `A ⊆ A₁`, `G₁ ⊆ A₂` and `G₂ ∩ A₂ ⊆ G`, then the
composition of the saturated delegates refines `(A, G)`. -/
theorem composeSat_refines {A G A₁ G₁ A₂ G₂ : Behaviours B}
    (hA : A ⊆ A₁) (hG₁ : G₁ ⊆ A₂) (hG₂ : (G₂ ∩ A₂) ⊆ G) :
    Contract.composeSat ⟨A₁, G₁⟩ ⟨A₂, G₂⟩ ⪯ ⟨A, G⟩ := by
  refine refines_iff.mpr ⟨fun x hx => ?_, fun x hx => ?_⟩
  · -- `A ⊆` the composed assumption: inside `G₁' ∩ G₂'` the point lies in `A₁ ∩ A₂`
    by_cases h : ((G₁ ∪ ∁ A₁) ∩ (G₂ ∪ ∁ A₂)) x
    · refine Or.inl ⟨hA x hx, ?_⟩
      rcases h.1 with h₁ | h₁
      · exact hG₁ x h₁
      · exact absurd (hA x hx) h₁
    · exact Or.inr h
  · -- the composed guarantee, on `A`, lies in `G`
    obtain ⟨⟨h₁, h₂⟩, hxA⟩ := hx
    have hA₁ : A₁ x := hA x hxA
    have hG₁x : G₁ x := by
      rcases h₁ with h | h
      · exact h
      · exact absurd hA₁ h
    have hA₂ : A₂ x := hG₁ x hG₁x
    have hG₂x : G₂ x := by
      rcases h₂ with h | h
      · exact h
      · exact absurd hA₂ h
    exact hG₂ x ⟨hG₂x, hA₂⟩

/-- Refinement is transitive. -/
theorem refines_trans {C₁ C₂ C₃ : Contract B} (h₁ : C₁ ⪯ C₂) (h₂ : C₂ ⪯ C₃) : C₁ ⪯ C₃ := by
  obtain ⟨a₁, g₁⟩ := refines_iff.mp h₁
  obtain ⟨a₂, g₂⟩ := refines_iff.mp h₂
  refine refines_iff.mpr ⟨fun x hx => a₁ x (a₂ x hx), fun x hx => ?_⟩
  exact g₂ x ⟨g₁ x ⟨hx.1, a₂ x hx.2⟩, hx.2⟩

/-- A contract refines its saturation. -/
theorem refines_saturate (C : Contract B) : C ⪯ saturate C :=
  refines_iff.mpr ⟨fun _ hx => hx, fun _ hx => Or.inl hx.1⟩

/-- The saturation refines the contract: the two are refinement-equivalent. -/
theorem saturate_refines (C : Contract B) : saturate C ⪯ C := by
  refine refines_iff.mpr ⟨fun _ hx => hx, fun x hx => ?_⟩
  rcases hx.1 with h | h
  · exact h
  · exact absurd hx.2 h

/-- The scheme against the saturated query: the composition of the saturated delegates also refines
`(A, G ∪ ∁A)`. -/
theorem composeSat_refines_saturate {A G A₁ G₁ A₂ G₂ : Behaviours B}
    (hA : A ⊆ A₁) (hG₁ : G₁ ⊆ A₂) (hG₂ : (G₂ ∩ A₂) ⊆ G) :
    Contract.composeSat ⟨A₁, G₁⟩ ⟨A₂, G₂⟩ ⪯ saturate ⟨A, G⟩ :=
  refines_trans (composeSat_refines hA hG₁ hG₂) (refines_saturate ⟨A, G⟩)

/-- Implementations compose: `M₁ ⊨ C₁` and `M₂ ⊨ C₂` give `M₁ ∥ M₂ ⊨ C₁ ∥ C₂` (saturated composition). -/
theorem implements_composeSat {M₁ M₂ : Behaviours B} {C₁ C₂ : Contract B}
    (h₁ : M₁ ⊨ C₁) (h₂ : M₂ ⊨ C₂) : M₁ ∥ M₂ ⊨ Contract.composeSat C₁ C₂ := by
  rw [implements_iff] at h₁ h₂ ⊢
  intro x hx
  obtain ⟨⟨hM₁, hM₂⟩, hAc⟩ := hx
  -- each saturated guarantee holds: either the point is in the assumption, and then in the guarantee, or not
  have g₁ : (C₁.G ∪ ∁ C₁.A) x := by
    by_cases h : C₁.A x
    · exact Or.inl (h₁ x ⟨hM₁, h⟩)
    · exact Or.inr h
  have g₂ : (C₂.G ∪ ∁ C₂.A) x := by
    by_cases h : C₂.A x
    · exact Or.inl (h₂ x ⟨hM₂, h⟩)
    · exact Or.inr h
  exact ⟨g₁, g₂⟩

/-- The delegation theorem a second way: compose the implementations, compose the contracts, refine.
-/
theorem delegation' {M₁ M₂ A G A₁ G₁ A₂ G₂ : Behaviours B}
    (hA : A ⊆ A₁) (hG₁ : G₁ ⊆ A₂) (hG₂ : (G₂ ∩ A₂) ⊆ G)
    (hM₁ : M₁ ⊨ ⟨A₁, G₁⟩) (hM₂ : M₂ ⊨ ⟨A₂, G₂⟩) :
    M₁ ⊗ M₂ ⊨ ⟨A, G⟩ :=
  rule_refinement (implements_composeSat hM₁ hM₂) (composeSat_refines hA hG₁ hG₂)

/-! ## One rule covers every composition

`implements_composeSat` is the general rule: no condition on the data flow. The named rules are this rule
followed by Assumption Relaxation and Guarantee Tightening, with a port condition used only to simplify the
composed assumption `(A₁ ∩ A₂) ∪ ∁(G₁' ∩ G₂')`. -/

/-- (Parallel) from the general rule: `A₁ ∩ A₂` is inside the composed assumption without any condition. -/
theorem rule_parallel_of_general {M₁ M₂ A₁ G₁ A₂ G₂ : Behaviours B}
    (h₁ : M₁ ⊨ ⟨A₁, G₁⟩) (h₂ : M₂ ⊨ ⟨A₂, G₂⟩) : M₁ ∥ M₂ ⊨ ⟨A₁ ∩ A₂, G₁ ∩ G₂⟩ := by
  have hc := implements_composeSat h₁ h₂
  have hr : M₁ ∥ M₂ ⊨ ⟨A₁ ∩ A₂, (G₁ ∪ ∁ A₁) ∩ (G₂ ∪ ∁ A₂)⟩ :=
    rule_assumption_relaxation hc (fun _ hx => Or.inl hx)
  refine rule_guarantee_tightening hr (fun x hx => ?_)
  obtain ⟨⟨g₁, g₂⟩, a₁, a₂⟩ := hx
  refine ⟨?_, ?_⟩
  · rcases g₁ with h | h
    · exact h
    · exact absurd a₁ h
  · rcases g₂ with h | h
    · exact h
    · exact absurd a₂ h

/-- (Composition) from the general rule: with `G₁ ⊆ A₂`, `A₁` is inside the composed assumption. -/
theorem rule_composition_of_general {M₁ M₂ A₁ G₁ A₂ G₂ : Behaviours B}
    (h₁ : M₁ ⊨ ⟨A₁, G₁⟩) (h₂ : M₂ ⊨ ⟨A₂, G₂⟩) (hG : G₁ ⊆ A₂) : M₁ ⊗ M₂ ⊨ ⟨A₁, G₂⟩ := by
  have hc := implements_composeSat h₁ h₂
  have hr : M₁ ⊗ M₂ ⊨ ⟨A₁, (G₁ ∪ ∁ A₁) ∩ (G₂ ∪ ∁ A₂)⟩ := by
    refine rule_assumption_relaxation hc (fun x hx => ?_)
    by_cases h : ((G₁ ∪ ∁ A₁) ∩ (G₂ ∪ ∁ A₂)) x
    · refine Or.inl ⟨hx, ?_⟩
      rcases h.1 with h' | h'
      · exact hG x h'
      · exact absurd hx h'
    · exact Or.inr h
  refine rule_guarantee_tightening hr (fun x hx => ?_)
  obtain ⟨⟨g₁, g₂⟩, a₁⟩ := hx
  have hG₁ : G₁ x := by
    rcases g₁ with h | h
    · exact h
    · exact absurd a₁ h
  rcases g₂ with h | h
  · exact h
  · exact absurd (hG x hG₁) h

/-- (Mixed) from the general rule: `M₂` reads outputs of `M₁` and environment variables, so its assumption is
established jointly, `E ∩ G₁ ⊆ A₂` with `E` the environment assumption. Then `M₁ ∥ M₂ ⊨ (E ∩ A₁, G₂)`. -/
theorem rule_mixed_of_general {M₁ M₂ E A₁ G₁ A₂ G₂ : Behaviours B}
    (h₁ : M₁ ⊨ ⟨A₁, G₁⟩) (h₂ : M₂ ⊨ ⟨A₂, G₂⟩) (hG : (E ∩ G₁) ⊆ A₂) : M₁ ⊗ M₂ ⊨ ⟨E ∩ A₁, G₂⟩ := by
  have hc := implements_composeSat h₁ h₂
  have hr : M₁ ⊗ M₂ ⊨ ⟨E ∩ A₁, (G₁ ∪ ∁ A₁) ∩ (G₂ ∪ ∁ A₂)⟩ := by
    refine rule_assumption_relaxation hc (fun x hx => ?_)
    by_cases h : ((G₁ ∪ ∁ A₁) ∩ (G₂ ∪ ∁ A₂)) x
    · refine Or.inl ⟨hx.2, ?_⟩
      rcases h.1 with h' | h'
      · exact hG x ⟨hx.1, h'⟩
      · exact absurd hx.2 h'
    · exact Or.inr h
  refine rule_guarantee_tightening hr (fun x hx => ?_)
  obtain ⟨⟨g₁, g₂⟩, e, a₁⟩ := hx
  have hG₁ : G₁ x := by
    rcases g₁ with h | h
    · exact h
    · exact absurd a₁ h
  rcases g₂ with h | h
  · exact h
  · exact absurd (hG x ⟨e, hG₁⟩) h

end AG
