import Mathlib.Data.Set.Basic
import Mathlib.Tactic.Tauto

/-!
# Contracts, implementation, refinement and composition

A behaviour is an element of a type `B`; a component, an assumption and a guarantee are sets of
behaviours. A contract is an assumption–guarantee pair and a component implements it when every
behaviour of the component that meets the assumption meets the guarantee. Composition of contracts is
saturated: each guarantee is first widened by the complement of its assumption.

Listing markers: a declaration the paper may show sits between the lines `-- <<name>>` and
`-- <</name>>`, where `name` is the declaration name (see `leanlst.tex` in the paper).
-/

namespace Contracts

variable {B : Type}

/-! ## Contracts and implementation -/

/-- A contract over behaviours `B` is an assumption `A` paired with a guarantee `G`. -/
-- <<Contract>>
structure Contract (B : Type) where
  /-- The assumption: the behaviours the environment is expected to produce. -/
  A : Set B
  /-- The guarantee: the behaviours the component promises under the assumption. -/
  G : Set B
-- <</Contract>>

/-- A component `M` implements `C` when its behaviours that meet `C.A` all meet `C.G`. -/
-- <<Implements>>
def Implements (M : Set B) (C : Contract B) : Prop := M ∩ C.A ⊆ C.G
/-- `M ⊨ C` is notation for `Implements M C`. -/
infix:50 " ⊨ " => Implements
-- <</Implements>>

/-- Implementation is equivalent to meeting the guarantee in every environment inside the assumption. -/
-- <<implements_iff_env>>
theorem implements_iff_env {M : Set B} {C : Contract B} :
    M ⊨ C ↔ ∀ E ⊆ C.A, M ∩ E ⊆ C.G :=
  ⟨fun h _ hE _ ⟨hM, hE'⟩ => h ⟨hM, hE hE'⟩, fun h => h C.A subset_rfl⟩
-- <</implements_iff_env>>

/-! ## Saturation and refinement -/

/-- The saturated guarantee of `C` adds every behaviour that violates the assumption. -/
-- <<saturate>>
def saturate (C : Contract B) : Set B := C.G ∪ C.Aᶜ
-- <</saturate>>

/-- A component implements a contract exactly when it lies inside the saturated guarantee. -/
-- <<implements_iff_saturate>>
theorem implements_iff_saturate {M : Set B} {C : Contract B} : M ⊨ C ↔ M ⊆ saturate C := by
  constructor
  · intro h b hb
    by_cases hA : b ∈ C.A
    · exact Or.inl (h ⟨hb, hA⟩)
    · exact Or.inr hA
  · rintro h b ⟨hb, hA⟩
    rcases h hb with hG | hnA
    · exact hG
    · exact absurd hA hnA
-- <</implements_iff_saturate>>

/-- `C₁` refines `C₂` when it assumes less and its saturated guarantee promises more. -/
-- <<Refines>>
def Refines (C₁ C₂ : Contract B) : Prop := C₂.A ⊆ C₁.A ∧ saturate C₁ ⊆ saturate C₂
/-- `C₁ ⪯ C₂` is notation for `Refines C₁ C₂`. -/
infix:50 " ⪯ " => Refines
-- <</Refines>>

/-- Every contract refines itself. -/
-- <<refines_refl>>
theorem refines_refl (C : Contract B) : C ⪯ C := ⟨subset_rfl, subset_rfl⟩
-- <</refines_refl>>

/-- Refinement is transitive. -/
-- <<refines_trans>>
theorem refines_trans {C₁ C₂ C₃ : Contract B} (h₁₂ : C₁ ⪯ C₂) (h₂₃ : C₂ ⪯ C₃) : C₁ ⪯ C₃ :=
  ⟨h₂₃.1.trans h₁₂.1, h₁₂.2.trans h₂₃.2⟩
-- <</refines_trans>>

/-- An implementation of a contract implements every contract that it refines. -/
-- <<refines_sound>>
theorem refines_sound {M : Set B} {C₁ C₂ : Contract B} (h : C₁ ⪯ C₂) (hM : M ⊨ C₁) : M ⊨ C₂ :=
  implements_iff_saturate.mpr fun _ hb => h.2 (implements_iff_saturate.mp hM hb)
-- <</refines_sound>>

/-! ## Composition -/

/-- The composite contract guarantees both saturated guarantees and assumes both assumptions,
relaxed by every behaviour outside the joint saturated guarantee. -/
-- <<comp>>
def comp (C₁ C₂ : Contract B) : Contract B :=
  ⟨(C₁.A ∩ C₂.A) ∪ (saturate C₁ ∩ saturate C₂)ᶜ, saturate C₁ ∩ saturate C₂⟩
/-- `C₁ ⊗ C₂` is notation for `comp C₁ C₂`. -/
infixl:70 " ⊗ " => comp
-- <</comp>>

/-- The saturated guarantee of a composite is the intersection of the saturated guarantees. -/
-- <<saturate_comp>>
theorem saturate_comp (C₁ C₂ : Contract B) : saturate (C₁ ⊗ C₂) = saturate C₁ ∩ saturate C₂ := by
  ext b
  simp only [saturate, comp, Set.mem_union, Set.mem_inter_iff, Set.mem_compl_iff, not_or, not_and,
    not_not]
  tauto
-- <</saturate_comp>>

/-- The intersection of implementations of two contracts implements their composite. -/
-- <<compose>>
theorem compose {M₁ M₂ : Set B} {C₁ C₂ : Contract B} (h₁ : M₁ ⊨ C₁) (h₂ : M₂ ⊨ C₂) :
    (M₁ ∩ M₂) ⊨ C₁ ⊗ C₂ :=
  implements_iff_saturate.mpr fun _ ⟨hb₁, hb₂⟩ =>
    Or.inl ⟨implements_iff_saturate.mp h₁ hb₁, implements_iff_saturate.mp h₂ hb₂⟩
-- <</compose>>

/-- If the composite of two component contracts refines a top-level contract, the intersection of
their implementations implements the top-level contract. -/
-- <<compose_refines>>
theorem compose_refines {M₁ M₂ : Set B} {C₁ C₂ C : Contract B}
    (h₁ : M₁ ⊨ C₁) (h₂ : M₂ ⊨ C₂) (h : C₁ ⊗ C₂ ⪯ C) : (M₁ ∩ M₂) ⊨ C :=
  refines_sound h (compose h₁ h₂)
-- <</compose_refines>>

/-- A component whose guarantee the second component may assume composes with it into an
implementation of the top-level contract. -/
-- <<chain>>
theorem chain {M₁ M₂ A G₁ G : Set B} (h₁ : M₁ ⊨ ⟨A, G₁⟩) (h₂ : M₂ ⊨ ⟨A ∩ G₁, G⟩) :
    (M₁ ∩ M₂) ⊨ ⟨A, G⟩ := by
  refine compose_refines h₁ h₂ ⟨?_, ?_⟩
  · intro b hA
    by_cases hG₁ : b ∈ G₁
    · exact Or.inl ⟨hA, hA, hG₁⟩
    · exact Or.inr fun ⟨hs, _⟩ => hs.elim hG₁ fun hnA => hnA hA
  · rw [saturate_comp]
    rintro b ⟨hs₁ | hnA₁, hG | hnA⟩
    · exact Or.inl hG
    · exact Or.inr fun hA => hnA ⟨hA, hs₁⟩
    · exact Or.inl hG
    · exact Or.inr hnA₁
-- <</chain>>

/-! ## The tightest contract of a component -/

/-- Every component implements the contract that guarantees its own behaviours. -/
-- <<tightest_implements>>
theorem tightest_implements (M A : Set B) : M ⊨ ⟨A, M ∪ Aᶜ⟩ :=
  fun _ hb => Or.inl hb.1
-- <</tightest_implements>>

/-- Among contracts with assumption `A` that `M` implements, the tightest one has the smallest
saturated guarantee. -/
-- <<tightest_saturate_subset>>
theorem tightest_saturate_subset {M A G : Set B} (h : M ⊨ ⟨A, G⟩) : saturate ⟨A, M ∪ Aᶜ⟩ ⊆ saturate ⟨A, G⟩ := by
  rintro b ((hM | hnA) | hnA)
  · exact implements_iff_saturate.mp h hM
  · exact Or.inr hnA
  · exact Or.inr hnA
-- <</tightest_saturate_subset>>

end Contracts
