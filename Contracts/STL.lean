import Mathlib.Data.Set.Basic
import Mathlib.Data.Real.Basic

/-!
# Discrete-time signal temporal logic

A trajectory is a state at every time index, `ℕ → X`. Formulas follow the paper's grammar: signal
predicates `f x ≥ 0` with `f : X → ℝ`, negation, conjunction, and the bounded always and
eventually operators. A time interval `[a, b]` is a set of time indices, so `□_[a,b] φ` at `t`
ranges over `τ ∈ [a + t, b + t]`.

A behaviour is a trajectory `ℕ → X` over the state type `X` of all system variables, so a formula
is directly a property, a set of behaviours: `lang φ` holds the behaviours satisfying `φ` at every
index, `init φ` those satisfying it at index `0`.
-/

namespace Contracts

namespace STL

/-- Formulas over a state type `X`. -/
inductive Formula (X : Type) where
  /-- The signal predicate `f x ≥ 0`. -/
  | atom (f : X → ℝ)
  | not (φ : Formula X)
  | and (φ ψ : Formula X)
  /-- `□_[a,b] φ` -/
  | always (a b : ℕ) (φ : Formula X)
  /-- `◇_[a,b] φ` -/
  | eventually (a b : ℕ) (φ : Formula X)

variable {X : Type}

/-- Boolean semantics: trajectory `x` satisfies the formula at time index `t`. -/
def sat (x : ℕ → X) : ℕ → Formula X → Prop
  | t, .atom f           => 0 ≤ f (x t)
  | t, .not φ            => ¬ sat x t φ
  | t, .and φ ψ          => sat x t φ ∧ sat x t ψ
  | t, .always a b φ     => ∀ τ, a + t ≤ τ → τ ≤ b + t → sat x τ φ
  | t, .eventually a b φ => ∃ τ, a + t ≤ τ ∧ τ ≤ b + t ∧ sat x τ φ

variable {x : ℕ → X} {t a b : ℕ} {φ ψ : Formula X}

@[simp] theorem sat_atom {f : X → ℝ} : sat x t (.atom f) ↔ 0 ≤ f (x t) := Iff.rfl
@[simp] theorem sat_not : sat x t φ.not ↔ ¬ sat x t φ := Iff.rfl
@[simp] theorem sat_and : sat x t (φ.and ψ) ↔ (sat x t φ) ∧ (sat x t ψ) := Iff.rfl
@[simp] theorem sat_always :
    sat x t (.always a b φ) ↔ ∀ τ, a + t ≤ τ → τ ≤ b + t → sat x τ φ := Iff.rfl
@[simp] theorem sat_eventually :
    sat x t (.eventually a b φ) ↔ ∃ τ, a + t ≤ τ ∧ τ ≤ b + t ∧ sat x τ φ := Iff.rfl

/-! ## Derived connectives -/

def Formula.or (φ ψ : Formula X) : Formula X := (φ.not.and ψ.not).not
def Formula.imp (φ ψ : Formula X) : Formula X := (φ.and ψ.not).not

@[simp] theorem sat_or : sat x t (φ.or ψ) ↔ (sat x t φ) ∨ (sat x t ψ) := by
  simp [Formula.or, or_iff_not_and_not]
@[simp] theorem sat_imp : sat x t (φ.imp ψ) ↔ ((sat x t φ) → sat x t ψ) := by
  simp [Formula.imp]

/-- Always and eventually are dual. -/
theorem sat_not_always : sat x t (Formula.always a b φ).not ↔ sat x t (.eventually a b φ.not) := by
  simp

/-! ## Formulas as properties over behaviours `ℕ → X` -/

/-- The behaviours satisfying `φ` at every time index. -/
def lang (φ : Formula X) : Set (ℕ → X) := {x | ∀ t, sat x t φ}

/-- The behaviours satisfying `φ` at time index `0`. -/
def init (φ : Formula X) : Set (ℕ → X) := {x | sat x 0 φ}

@[simp] theorem mem_lang : x ∈ lang φ ↔ ∀ t, sat x t φ := Iff.rfl
@[simp] theorem mem_init : x ∈ init φ ↔ sat x 0 φ := Iff.rfl

theorem lang_subset_init : lang φ ⊆ init φ := fun _ h => h 0

theorem lang_and : lang (φ.and ψ) = lang φ ∩ lang ψ := by
  ext x; simp [forall_and]

/-! ## Horizon -/

/-- How far past `t` the semantics of a formula looks. -/
def Formula.hrz : Formula X → ℕ
  | .atom _           => 0
  | .not φ            => φ.hrz
  | .and φ ψ          => max φ.hrz ψ.hrz
  | .always _ b φ     => b + 1 + φ.hrz
  | .eventually _ b φ => b + 1 + φ.hrz

/-- The reach-and-hold formula `◇_[0,10] □_[0,2] (y ≥ 5)` of the paper has horizon `14`. -/
example : (Formula.eventually 0 10 (.always 0 2 (.atom fun y : ℝ => y - 5))).hrz = 14 := rfl

/-- Satisfaction at `t` depends only on the trajectory on `[t, t + hrz φ]`, so it is decided by a
finite trace of that length. -/
theorem sat_congr (φ : Formula X) : ∀ (t : ℕ) (x y : ℕ → X),
    (∀ τ, t ≤ τ → τ ≤ t + φ.hrz → x τ = y τ) → ((sat x t φ) ↔ (sat y t φ)) := by
  induction φ with
  | atom f => intro t x y h; simp [h t le_rfl (by simp [Formula.hrz])]
  | not φ ih => intro t x y h; exact not_congr (ih t x y h)
  | and φ ψ ihφ ihψ =>
    intro t x y h
    exact and_congr (ihφ t x y fun τ h₁ h₂ => h τ h₁ (by simp [Formula.hrz] at *; omega))
      (ihψ t x y fun τ h₁ h₂ => h τ h₁ (by simp [Formula.hrz] at *; omega))
  | always a b φ ih =>
    intro t x y h
    exact forall_congr' fun τ => imp_congr_right fun h₁ => imp_congr_right fun h₂ =>
      ih τ x y fun σ h₃ h₄ => h σ (by omega) (by simp [Formula.hrz] at *; omega)
  | eventually a b φ ih =>
    intro t x y h
    exact exists_congr fun τ => and_congr_right fun h₁ => and_congr_right fun h₂ =>
      ih τ x y fun σ h₃ h₄ => h σ (by omega) (by simp [Formula.hrz] at *; omega)

end STL

end Contracts
