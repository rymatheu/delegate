module

public import Contracts.STL
public import Contracts.Basic

@[expose] public section

/-!
# The invariant rule: always-operators on untimed formulas are discharged by induction

An untimed formula is built from signal predicates by negation and conjunction; whether a behaviour
satisfies it at an index depends on the state at that index alone (`sat_untimed`), so it names a
set of states, `holds φ`. For a module whose behaviours step by a relation `R` (the closed loop,
deterministic or not), `□_[a,b] φ` at `t` follows from a time-indexed family of state sets `I`:
the behaviours' states at the window's first index lie in `I (a + t)` (the base, taken on the
assumption in the contract form), one step inside the window stays in the family (the inductive
step), and every member of the family inside the window lies in `holds φ` (the target). Induction
on the index gives that every reachable state of the window lies in the family
(`always_of_invariant`). The classical rule with one set closed under the step is the constant
family (`always_of_invariant_const`). The slack of the step and of the target inclusions is the
quantitative margin of a proof by this rule.
-/

namespace Contracts.STL

variable {X : Type}

/-- Untimed formulas: signal predicates under negation and conjunction, no temporal operator. -/
inductive Untimed : Formula X → Prop
  | atom (f : X → ℝ) : Untimed (.atom f)
  | not {φ : Formula X} : Untimed φ → Untimed φ.not
  | and {φ ψ : Formula X} : Untimed φ → Untimed ψ → Untimed (φ.and ψ)

/-- The states satisfying a formula, read at one state (meaningful for untimed formulas; the
temporal cases are placeholders never used). -/
def holds : Formula X → X → Prop
  | .atom f, s => 0 ≤ f s
  | .not φ, s => ¬ holds φ s
  | .and φ ψ, s => holds φ s ∧ holds ψ s
  | .always _ _ _, _ => True
  | .eventually _ _ _, _ => True

/-- An untimed formula holds at an index exactly when the state at that index satisfies it. -/
theorem sat_untimed {φ : Formula X} (h : Untimed φ) (x : ℕ → X) (t : ℕ) :
    sat x t φ ↔ holds φ (x t) := by
  induction h with
  | atom f => exact Iff.rfl
  | not _ ih => rw [sat_not, ih]; exact Iff.rfl
  | and _ _ ih₁ ih₂ => rw [sat_and, ih₁, ih₂]; exact Iff.rfl

/-- **The invariant rule.** Behaviours of `M` step by `R`; the family `I` contains their states
at index `a + t`, is closed under one step inside the window, and lies inside the states of the
untimed `φ` on the window; then every behaviour of `M` satisfies `□_[a,b] φ` at `t`. -/
theorem always_of_invariant {M : Set (ℕ → X)} {R : X → X → Prop}
    (hstep : ∀ x ∈ M, ∀ k, R (x k) (x (k + 1)))
    (I : ℕ → Set X) {φ : Formula X} (hφ : Untimed φ) (t a b : ℕ)
    (hbase : ∀ x ∈ M, x (a + t) ∈ I (a + t))
    (hind : ∀ τ, a + t ≤ τ → τ < b + t → ∀ s ∈ I τ, ∀ s', R s s' → s' ∈ I (τ + 1))
    (htarget : ∀ τ, a + t ≤ τ → τ ≤ b + t → ∀ s ∈ I τ, holds φ s) :
    ∀ x ∈ M, sat x t (.always a b φ) := by
  intro x hx
  rw [sat_always]
  have key : ∀ n, a + t + n ≤ b + t → x (a + t + n) ∈ I (a + t + n) := by
    intro n
    induction n with
    | zero => intro _; simpa using hbase x hx
    | succ n ih =>
      intro hn
      have h := hind (a + t + n) (by omega) (by omega) _ (ih (by omega)) _ (hstep x hx (a + t + n))
      exact h
  intro τ h₁ h₂
  obtain ⟨n, rfl⟩ : ∃ n, τ = a + t + n := ⟨τ - (a + t), by omega⟩
  rw [sat_untimed hφ]
  exact htarget _ h₁ h₂ _ (key n h₂)

/-- The classical rule: one set closed under the step. -/
theorem always_of_invariant_const {M : Set (ℕ → X)} {R : X → X → Prop}
    (hstep : ∀ x ∈ M, ∀ k, R (x k) (x (k + 1)))
    (I : Set X) {φ : Formula X} (hφ : Untimed φ) (t a b : ℕ)
    (hbase : ∀ x ∈ M, x (a + t) ∈ I)
    (hind : ∀ s ∈ I, ∀ s', R s s' → s' ∈ I)
    (htarget : ∀ s ∈ I, holds φ s) :
    ∀ x ∈ M, sat x t (.always a b φ) :=
  always_of_invariant hstep (fun _ => I) hφ t a b hbase (fun _ _ _ s hs s' h => hind s hs s' h)
    (fun _ _ _ s hs => htarget s hs)

/-- **The contract form**: the base case is taken on the behaviours inside the assumption `A`,
and the guarantee is the language of `□_[a,b] φ` at `t`. -/
theorem implements_always_of_invariant {M A : Set (ℕ → X)} {R : X → X → Prop}
    (hstep : ∀ x ∈ M, ∀ k, R (x k) (x (k + 1)))
    (I : ℕ → Set X) {φ : Formula X} (hφ : Untimed φ) (t a b : ℕ)
    (hbase : ∀ x ∈ M ∩ A, x (a + t) ∈ I (a + t))
    (hind : ∀ τ, a + t ≤ τ → τ < b + t → ∀ s ∈ I τ, ∀ s', R s s' → s' ∈ I (τ + 1))
    (htarget : ∀ τ, a + t ≤ τ → τ ≤ b + t → ∀ s ∈ I τ, holds φ s) :
    M ⊨ ⟨A, {x | sat x t (.always a b φ)}⟩ :=
  fun x hx =>
    always_of_invariant (M := M ∩ A) (fun y hy k => hstep y hy.1 k) I hφ t a b hbase hind htarget x hx

end Contracts.STL
