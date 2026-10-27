import Composition
/-!
# Delegation along a chain of `n` components

A chain `M₁ ⊗ M₂ ⊗ ⋯ ⊗ Mₙ` with delegates `(A₁, G₁), …, (Aₙ, Gₙ)`. The constraints are
`A ⊆ A₁`, the edge conditions `Gᵢ ⊆ Aᵢ₊₁` for `i < n`, and `Gₙ ∩ Aₙ ⊆ G`. Then the composition of any
implementations of the delegates implements `(A, G)`. The proof is the two-component proof iterated: tighten the
last guarantee, compose along the edges from the end, relax the first assumption. Lists are written head-and-tail
(`M :: Ms`, `C :: Cs`) so that every function is total and the two-component case is literally `delegation`.
-/

namespace AG

variable {B : Type}

/-- Sequential composition of a non-empty list of components, `M₁ ∥ (M₂ ∥ (⋯ ∥ Mₙ))`. -/
def composeAll : Behaviours B → List (Behaviours B) → Behaviours B
  | M, [] => M
  | M, M' :: Ms => M ∥ composeAll M' Ms

/-- Each component implements its contract (the lists must have the same length). -/
def ImplementsAll : List (Behaviours B) → List (Contract B) → Prop
  | [], [] => True
  | M :: Ms, C :: Cs => M ⊨ C ∧ ImplementsAll Ms Cs
  | _, _ => False

/-- Edge conditions along a chain `C :: Cs`: each guarantee establishes the next assumption. -/
def Chain : Contract B → List (Contract B) → Prop
  | _, [] => True
  | C, C' :: Cs => C.G ⊆ C'.A ∧ Chain C' Cs

/-- The last contract of a non-empty chain. -/
def lastC : Contract B → List (Contract B) → Contract B
  | C, [] => C
  | _, C' :: Cs => lastC C' Cs

/-- Composition along a chain with the last guarantee tightened to `G`: the composite implements `(A₁, G)`. -/
theorem chain_compose {G : Behaviours B} :
    ∀ (Cs : List (Contract B)) (M : Behaviours B) (Ms : List (Behaviours B)) (C : Contract B),
      ImplementsAll (M :: Ms) (C :: Cs) → Chain C Cs → ((lastC C Cs).G ∩ (lastC C Cs).A) ⊆ G →
      composeAll M Ms ⊨ ⟨C.A, G⟩
  | [], M, Ms, C, hImpl, _, hG => by
      cases Ms with
      | nil => exact rule_guarantee_tightening hImpl.1 hG
      | cons _ _ => exact hImpl.2.elim
  | C₂ :: Cs, M, Ms, C, hImpl, hChain, hG => by
      cases Ms with
      | nil => exact hImpl.2.elim
      | cons M₂ Ms =>
        have ih := chain_compose Cs M₂ Ms C₂ hImpl.2 hChain.2 hG
        exact rule_composition hImpl.1 ih hChain.1

/-- The chain delegation theorem. Delegates `C :: Cs` for components `M :: Ms`; if `A ⊆ A₁`, the edge
conditions hold along the chain, `Gₙ ∩ Aₙ ⊆ G`, and each component implements its delegate, then the
composition of the components implements `(A, G)`. -/
theorem chain_delegation {A G : Behaviours B}
    (M : Behaviours B) (Ms : List (Behaviours B)) (C : Contract B) (Cs : List (Contract B))
    (hImpl : ImplementsAll (M :: Ms) (C :: Cs)) (hChain : Chain C Cs)
    (hA : A ⊆ C.A) (hG : ((lastC C Cs).G ∩ (lastC C Cs).A) ⊆ G) :
    composeAll M Ms ⊨ ⟨A, G⟩ :=
  rule_assumption_relaxation (chain_compose Cs M Ms C hImpl hChain hG) hA

/-- The two-component case is `delegation`. -/
example {M₁ M₂ A G A₁ G₁ A₂ G₂ : Behaviours B}
    (hA : A ⊆ A₁) (hG₁ : G₁ ⊆ A₂) (hG₂ : (G₂ ∩ A₂) ⊆ G)
    (hM₁ : M₁ ⊨ ⟨A₁, G₁⟩) (hM₂ : M₂ ⊨ ⟨A₂, G₂⟩) : M₁ ⊗ M₂ ⊨ ⟨A, G⟩ :=
  chain_delegation M₁ [M₂] ⟨A₁, G₁⟩ [⟨A₂, G₂⟩] ⟨hM₁, hM₂, trivial⟩ ⟨hG₁, trivial⟩ hA hG₂

/-- A three-component instance, spelled out. -/
example {M₁ M₂ M₃ A G A₁ G₁ A₂ G₂ A₃ G₃ : Behaviours B}
    (hA : A ⊆ A₁) (h₁₂ : G₁ ⊆ A₂) (h₂₃ : G₂ ⊆ A₃) (hG : (G₃ ∩ A₃) ⊆ G)
    (hM₁ : M₁ ⊨ ⟨A₁, G₁⟩) (hM₂ : M₂ ⊨ ⟨A₂, G₂⟩) (hM₃ : M₃ ⊨ ⟨A₃, G₃⟩) :
    M₁ ⊗ (M₂ ⊗ M₃) ⊨ ⟨A, G⟩ :=
  chain_delegation M₁ [M₂, M₃] ⟨A₁, G₁⟩ [⟨A₂, G₂⟩, ⟨A₃, G₃⟩]
    ⟨hM₁, hM₂, hM₃, trivial⟩ ⟨h₁₂, h₂₃, trivial⟩ hA hG

/-! ## The contracts themselves: the composition of the saturated delegates refines the query -/

/-- Composition of the saturated delegates along a chain, nested to the right:
`sat C₁ ∥ (sat C₂ ∥ (⋯ ∥ sat Cₙ))`. -/
def composeChainSat : Contract B → List (Contract B) → Contract B
  | C, [] => saturate C
  | C, C' :: Cs => Contract.compose (saturate C) (composeChainSat C' Cs)

/-- One edge: if `D ⪯ (A₂, G)` and `G₁ ⊆ A₂`, then `sat (A₁, G₁) ∥ D ⪯ (A₁, G)`. -/
theorem compose_sat_refines_step {A₁ G₁ A₂ G : Behaviours B} {D : Contract B}
    (hD : D ⪯ ⟨A₂, G⟩) (hG₁ : G₁ ⊆ A₂) :
    Contract.compose (saturate ⟨A₁, G₁⟩) D ⪯ ⟨A₁, G⟩ := by
  obtain ⟨hDA, hDG⟩ := refines_iff.mp hD
  refine refines_iff.mpr ⟨fun x hx => ?_, fun x hx => ?_⟩
  · by_cases h : ((G₁ ∪ ∁ A₁) ∩ D.G) x
    · refine Or.inl ⟨hx, ?_⟩
      rcases h.1 with h₁ | h₁
      · exact hDA x (hG₁ x h₁)
      · exact absurd hx h₁
    · exact Or.inr h
  · obtain ⟨⟨h₁, hDGx⟩, hA₁⟩ := hx
    have hG₁x : G₁ x := by
      rcases h₁ with h | h
      · exact h
      · exact absurd hA₁ h
    exact hDG x ⟨hDGx, hG₁ x hG₁x⟩

/-- Along a chain with `Gₙ ∩ Aₙ ⊆ G`, the composition of the saturated delegates refines `(A₁, G)`. -/
theorem composeChainSat_refines_head {G : Behaviours B} :
    ∀ (Cs : List (Contract B)) (C : Contract B),
      Chain C Cs → ((lastC C Cs).G ∩ (lastC C Cs).A) ⊆ G → composeChainSat C Cs ⪯ ⟨C.A, G⟩
  | [], C, _, hG => by
      refine refines_iff.mpr ⟨fun _ hx => hx, fun x hx => ?_⟩
      rcases hx.1 with h | h
      · exact hG x ⟨h, hx.2⟩
      · exact absurd hx.2 h
  | C₂ :: Cs, C, hChain, hG =>
      compose_sat_refines_step (composeChainSat_refines_head Cs C₂ hChain.2 hG) hChain.1

/-- The composition of the saturated delegates refines the query `(A, G)`: with `A ⊆ A₁`, the edge
conditions, and `Gₙ ∩ Aₙ ⊆ G`. No implementation hypotheses are needed. -/
theorem composeChainSat_refines {A G : Behaviours B} (C : Contract B) (Cs : List (Contract B))
    (hChain : Chain C Cs) (hA : A ⊆ C.A) (hG : ((lastC C Cs).G ∩ (lastC C Cs).A) ⊆ G) :
    composeChainSat C Cs ⪯ ⟨A, G⟩ := by
  have h := refines_iff.mp (composeChainSat_refines_head Cs C hChain hG)
  exact refines_iff.mpr ⟨fun x hx => h.1 x (hA x hx), fun x hx => h.2 x ⟨hx.1, hA x hx.2⟩⟩

/-- The same against the saturated query. -/
theorem composeChainSat_refines_saturate {A G : Behaviours B} (C : Contract B) (Cs : List (Contract B))
    (hChain : Chain C Cs) (hA : A ⊆ C.A) (hG : ((lastC C Cs).G ∩ (lastC C Cs).A) ⊆ G) :
    composeChainSat C Cs ⪯ saturate ⟨A, G⟩ :=
  refines_trans (composeChainSat_refines C Cs hChain hA hG) (refines_saturate ⟨A, G⟩)

/-! ## Big-operator forms: `⊗ M ∈ Ms, M` for a chain, `∥ M ∈ Ms, M` for a parallel bundle -/

/-- The unit of both compositions: every behaviour. -/
def top : Behaviours B := fun _ => True

/-- Sequential big operator: `BigSeq [M₁, …, Mₙ] = M₁ ⊗ (⋯ ⊗ (Mₙ ⊗ top))`. -/
def BigSeq : List (Behaviours B) → Behaviours B
  | [] => top
  | M :: Ms => M ⊗ BigSeq Ms

/-- Parallel big operator: `BigPar [M₁, …, Mₙ] = M₁ ∥ (⋯ ∥ (Mₙ ∥ top))`. -/
def BigPar : List (Behaviours B) → Behaviours B
  | [] => top
  | M :: Ms => M ∥ BigPar Ms

syntax "⊗ " ident " ∈ " term ", " term:67 : term
macro_rules
  | `(⊗ $x ∈ $l, $f) => `(BigSeq (List.map (fun $x => $f) $l))

syntax "∥ " ident " ∈ " term ", " term:67 : term
macro_rules
  | `(∥ $x ∈ $l, $f) => `(BigPar (List.map (fun $x => $f) $l))

theorem seq_top (M : Behaviours B) : M ⊗ top = M := by
  funext x
  exact propext ⟨fun h => h.1, fun h => ⟨h, trivial⟩⟩

theorem par_top (M : Behaviours B) : M ∥ top = M := seq_top M

/-- The sequential big operator agrees with the nested composition of the chain theorem. -/
theorem bigSeq_cons (M : Behaviours B) (Ms : List (Behaviours B)) : BigSeq (M :: Ms) = composeAll M Ms := by
  induction Ms generalizing M with
  | nil => exact seq_top M
  | cons M' Ms ih =>
    show M ⊗ BigSeq (M' :: Ms) = M ⊗ composeAll M' Ms
    rw [ih M']

/-- The chain delegation theorem in big-operator form. -/
theorem chain_delegation_bigSeq {A G : Behaviours B}
    (M : Behaviours B) (Ms : List (Behaviours B)) (C : Contract B) (Cs : List (Contract B))
    (hImpl : ImplementsAll (M :: Ms) (C :: Cs)) (hChain : Chain C Cs)
    (hA : A ⊆ C.A) (hG : ((lastC C Cs).G ∩ (lastC C Cs).A) ⊆ G) :
    (⊗ N ∈ (M :: Ms), N) ⊨ ⟨A, G⟩ := by
  show BigSeq (List.map (fun N => N) (M :: Ms)) ⊨ _
  rw [List.map_id_fun', id, bigSeq_cons]
  exact chain_delegation M Ms C Cs hImpl hChain hA hG

/-- The notations with a family. -/
example (f : Nat → Behaviours B) : (⊗ i ∈ [0, 1, 2], f i) = f 0 ⊗ (f 1 ⊗ (f 2 ⊗ top)) := rfl
example (f : Nat → Behaviours B) : (∥ i ∈ [0, 1, 2], f i) = f 0 ∥ (f 1 ∥ (f 2 ∥ top)) := rfl

/-! ## Any DAG is an iterated pure sequential composition

List the components in a topological order with the environment first. Because nothing is hidden, the
composite built so far outputs every variable produced so far, so each next component reads only outputs of
the composite: every step is a pure sequential composition. The edge condition at step `i` uses the
accumulated guarantee: `A_E ∩ ⋂_{j<i} Gⱼ ⊆ Aᵢ`. This is the node rule of a DAG, and the theorem below is the
DAG delegation theorem for any topological order. -/

/-- Accumulated edge conditions: `Acc K C Cs` says `K ⊆ C.A`, and then, with `K ∩ C.G` accumulated, the same
for the rest. `K` starts as the environment assumption. -/
def Acc : Behaviours B → Contract B → List (Contract B) → Prop
  | K, C, [] => K ⊆ C.A
  | K, C, C' :: Cs => K ⊆ C.A ∧ Acc (K ∩ C.G) C' Cs

/-- The intersection of all guarantees of a non-empty list of contracts. -/
def allG : Contract B → List (Contract B) → Behaviours B
  | C, [] => C.G
  | C, C' :: Cs => C.G ∩ allG C' Cs

/-- Iterated pure sequential composition with accumulated guarantees: under `K`, the composite guarantees
every delegate's guarantee. -/
theorem acc_compose :
    ∀ (Cs : List (Contract B)) (K M : Behaviours B) (Ms : List (Behaviours B)) (C : Contract B),
      ImplementsAll (M :: Ms) (C :: Cs) → Acc K C Cs → composeAll M Ms ⊨ ⟨K, allG C Cs⟩
  | [], K, M, Ms, C, hImpl, hAcc => by
      cases Ms with
      | nil => exact rule_assumption_relaxation hImpl.1 hAcc
      | cons _ _ => exact hImpl.2.elim
  | C₂ :: Cs, K, M, Ms, C, hImpl, hAcc => by
      cases Ms with
      | nil => exact hImpl.2.elim
      | cons M₂ Ms =>
        have ih := acc_compose Cs (K ∩ C.G) M₂ Ms C₂ hImpl.2 hAcc.2
        -- the general rule with A := K: K ⊆ C.A and K ∩ C.G ⊆ (K ∩ C.G), the next composite's assumption
        show M ⊗ composeAll M₂ Ms ⊨ ⟨K, C.G ∩ allG C₂ Cs⟩
        exact rule_general hImpl.1 ih hAcc.1 (fun _ hx => hx)

/-- The DAG delegation theorem. Components in a topological order with contracts `C :: Cs`; if the
accumulated edge conditions hold from the environment assumption `A`, and all guarantees together deliver
`G` under `A`, then the composition implements `(A, G)`. -/
theorem dag_delegation {A G : Behaviours B}
    (M : Behaviours B) (Ms : List (Behaviours B)) (C : Contract B) (Cs : List (Contract B))
    (hImpl : ImplementsAll (M :: Ms) (C :: Cs)) (hAcc : Acc A C Cs)
    (hG : (allG C Cs ∩ A) ⊆ G) :
    composeAll M Ms ⊨ ⟨A, G⟩ :=
  rule_guarantee_tightening (acc_compose Cs A M Ms C hImpl hAcc) hG

/-- The chain conditions are a special case: consecutive edges imply the accumulated ones. -/
theorem chain_delegation_of_dag {A G : Behaviours B}
    (M : Behaviours B) (Ms : List (Behaviours B)) (C : Contract B) (Cs : List (Contract B))
    (hImpl : ImplementsAll (M :: Ms) (C :: Cs)) (hChain : Chain C Cs)
    (hA : A ⊆ C.A) (hG : ((lastC C Cs).G ∩ (lastC C Cs).A) ⊆ G) :
    composeAll M Ms ⊨ ⟨A, G⟩ := by
  refine dag_delegation M Ms C Cs hImpl ?_ ?_
  · -- accumulated conditions from consecutive ones
    have key : ∀ (Cs : List (Contract B)) (K : Behaviours B) (C : Contract B),
        K ⊆ C.A → Chain C Cs → Acc K C Cs := by
      intro Cs
      induction Cs with
      | nil => intro K C hK _; exact hK
      | cons C₂ Cs ih =>
        intro K C hK hChain
        exact ⟨hK, ih (K ∩ C.G) C₂ (fun _ hx => hChain.1 _ hx.2) hChain.2⟩
    exact key Cs A C hA hChain
  · -- the last guarantee under the last assumption: the last assumption holds under A and the earlier guarantees
    have key : ∀ (Cs : List (Contract B)) (K : Behaviours B) (C : Contract B),
        K ⊆ C.A → Chain C Cs → (allG C Cs ∩ K) ⊆ ((lastC C Cs).G ∩ (lastC C Cs).A) := by
      intro Cs
      induction Cs with
      | nil => intro K C hK _ x hx; exact ⟨hx.1, hK x hx.2⟩
      | cons C₂ Cs ih =>
        intro K C hK hChain x hx
        exact ih (K ∩ C.G) C₂ (fun _ hy => hChain.1 _ hy.2) hChain.2 x ⟨hx.1.2, hx.2, hx.1.1⟩
    exact fun x hx => hG x (key Cs A C hA hChain x hx)

end AG
