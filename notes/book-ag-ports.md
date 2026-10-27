# What the Benveniste et al. report (book/) does with ports, in our terms (2026-10-26)

Source: "Contracts for System Design", INRIA RR-8147 (2012), Sections IV, V, VII. Own summary, own words.

- Meta-theory (V): components with a partial, associative, commutative composition ×; composability is a typing
  property. A contract is a pair (set of environments, set of implementations). Refinement = fewer implementations,
  more environments. Contract composition is defined from component composition so that implementations compose
  and environments split. Quotient = adjoint of composition. No ports at this level.
- A/G with one alphabet (VII-A): a component is a set of behaviours P over a fixed alphabet Σ (flows per variable;
  the synchronous variant (18) uses sequences of reactions, which is our timed-trace model at bounded horizon).
  Composition is intersection, always defined. Contract (A, G): environments E ⊆ A, implementations A ∩ M ⊆ G;
  saturation G ∪ ¬A; refinement (12); composition (14). "No quotient is known for A/G contracts" (2012).
- Inputs and outputs (VII-B): component M = (Σin, Σout, P). Composable iff Σout₁ ∩ Σout₂ = ∅. Then
  M₁ × M₂ = (Σin, Σout, P₁ ∩ P₂), Σout = Σout₁ ∪ Σout₂, Σin = Σ − Σout. "Free of exception" = accepts all inputs
  (pr_Σin(P) = all input flows: our receptiveness) and does not itself produce fail. Contract C = (Σin, Σout, A, G);
  environments have the mirrored ports and P_E ⊆ A; implementations have C's ports, are exception free, and
  P_{E×M} ⊆ G for every environment (same as A ∩ M ⊆ G). Property 7: consistent and compatible if G is input
  enabled (pr_Σin(G) = all), A does not constrain outputs (pr_Σout(A) = all), no fail in G ∧ A.
- Variable alphabets (VII-C): component (Σ_M, P_M); contract (Σ_C, A_C, G_C). Alphabet equalization = inverse
  projection pr⁻¹ to the union alphabet, outputs kept, inputs = the rest; then reuse the fixed-alphabet
  definitions. This is exactly "cylinder over the component's variables" when one global alphabet is used.
- Types (IV): "composable if their variable types match"; a type is the domain of a variable. Nothing beyond
  domain agreement on shared variables.
- There is no sequential composition in the book. One operator ×; whether two components are side by side or one
  feeds the other is read off Σout₁ ∩ Σin₂ and Σout₂ ∩ Σin₁.

Mapping to ours: our behaviours = synchronous reactions over V at times 0..H with real domains; our port-local
sets = inverse projections; our (P) = alphabet discipline; our (R) = "accepts all inputs"; our (K) is not in the
book (causality is left to the component model). Our delegation scheme (A ⊆ A₁, G₁ ⊆ A₂, G₂ ∩ A₂ ⊆ G) is a
per-edge sufficient condition for the book's decomposition criterion C₁ ⊗ C₂ ⪯ C.
