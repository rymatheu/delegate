import Contracts.Invariant
import Contracts.Mission.Spec

/-!
# The invariant rule on histories (REACH.md §11)

The tracking box of the leg theorems (`leg_box`, `leg_box3`) is not a set of states of the loop
universe `X`: its readouts `ξV`, `ξH` read the controller's world `run w₀ x t`, which is
reconstructed from the samples of all earlier ticks, and the box at `t + 1` follows from the box at
**every** earlier tick (the ℓ1 envelopes are convolutions over the past), not from the box at `t`
alone. So the invariant rule `Contracts.STL.always_of_invariant` is instantiated here on the
**history** state: the extended state at tick `τ` is the prefix `pre x τ` of the behavior (the states
of ticks `0 … τ`, which determine `run w₀ x τ` and every readout up to `τ`), the extended behavior is
`hist x = pre x`, and the step relation `histStep M` is one tick of the module on histories: `s'` is
the next prefix of a behavior of `M` whose prefix is `s`.

`implements_always_of_prefix` is the instance: from a per-behavior predicate `Box x k` that holds at
`τ ≥ t₀` whenever it held on `[t₀, τ)` (a strong-induction step, the form of `leg_box`), a target
`Box x τ → 0 ≤ f (x τ)` and the ticks before `t₀`, every behavior of `M` inside an assumption that
reads tick 0 only satisfies `□_[0,T] (f ≥ 0)`. The family `I τ` handed to
`implements_always_of_invariant` is the set of histories of length `τ` that are prefixes of a
behavior of `M ∩ A` and on which every such behavior has had the box on `[t₀, τ]`; its base, its
inductive step and its target inclusion are the three hypotheses.
-/

namespace Contracts.Track.Reach.Safe

open Contracts Contracts.STL

variable {X : Type}

/-- A history: the states of the ticks `0 … len` (the function is read on `[0, len]`). -/
structure Hist (X : Type) where
  /-- The last tick of the history. -/
  len : ℕ
  /-- The states (read on `[0, len]`). -/
  st : ℕ → X

/-- The state at the last tick of a history. -/
def Hist.last (s : Hist X) : X := s.st s.len

/-- The prefix of a behavior up to tick `τ` (frozen after `τ`). -/
def pre (x : ℕ → X) (τ : ℕ) : Hist X := ⟨τ, fun k => x (min k τ)⟩

/-- **The extended behavior**: at every tick the history so far. -/
def hist (x : ℕ → X) : ℕ → Hist X := pre x

/-- **One tick of a module on histories**: `s'` is the next prefix of a behavior of `M` whose prefix
is `s`. -/
def histStep (M : Set (ℕ → X)) (s s' : Hist X) : Prop :=
  ∃ x ∈ M, s = pre x s.len ∧ s' = pre x (s.len + 1)

@[simp] theorem pre_len (x : ℕ → X) (τ : ℕ) : (pre x τ).len = τ := rfl

@[simp] theorem pre_last (x : ℕ → X) (τ : ℕ) : (pre x τ).last = x τ := by
  simp [pre, Hist.last]

/-- Two prefixes up to `τ` are equal exactly when the behaviors agree on `[0, τ]`. -/
theorem pre_eq_iff {x y : ℕ → X} {τ : ℕ} : pre x τ = pre y τ ↔ ∀ k ≤ τ, x k = y k := by
  constructor
  · intro h k hk
    have := congrArg (fun s : Hist X => s.st k) h
    simpa [pre, min_eq_left hk] using this
  · intro h
    simp only [pre, Hist.mk.injEq, true_and]
    funext k
    exact h _ (min_le_right _ _)

/-- The behaviors of a module, lifted to histories, step by `histStep`. -/
theorem hist_step (M : Set (ℕ → X)) : ∀ xh ∈ hist '' M, ∀ k, histStep M (xh k) (xh (k + 1)) := by
  rintro _ ⟨x, hx, rfl⟩ k
  exact ⟨x, hx, rfl, rfl⟩

/-- **The invariant rule on histories.** `Box x k` holds at every `τ ≥ t₀` at which it held on
`[t₀, τ)` (for the behaviors of `M` inside `A`), implies `f ≥ 0` there, and `f ≥ 0` holds before
`t₀`; `A` reads tick 0 only. Then `M ⊨ ⟨A, □_[0,T] (f ≥ 0)⟩`, by
`implements_always_of_invariant` on the history state with the family described in the module
docstring. -/
theorem implements_always_of_prefix {M A : Set (ℕ → X)} (hA : ∀ x y, x 0 = y 0 → x ∈ A → y ∈ A)
    (Box : (ℕ → X) → ℕ → Prop) (t₀ : ℕ) (f : X → ℝ) (T : ℕ)
    (hstep : ∀ x ∈ M ∩ A, ∀ τ, t₀ ≤ τ → (∀ k, t₀ ≤ k → k < τ → Box x k) → Box x τ)
    (hearly : ∀ x ∈ M ∩ A, ∀ τ < t₀, 0 ≤ f (x τ))
    (htarget : ∀ x ∈ M ∩ A, ∀ τ, t₀ ≤ τ → Box x τ → 0 ≤ f (x τ)) :
    M ⊨ ⟨A, lang_t 0 (.always 0 T (.atom f))⟩ := by
  -- the family: prefixes of behaviors of `M ∩ A` on which every such behavior had the box
  let I : ℕ → Set (Hist X) := fun τ => {s | s.len = τ ∧ (∃ x ∈ M ∩ A, s = pre x τ) ∧
    ∀ y ∈ M ∩ A, s = pre y τ → ∀ k, t₀ ≤ k → k ≤ τ → Box y k}
  have rule := implements_always_of_invariant (M := hist '' M) (A := hist '' A)
    (hist_step M) I (Untimed.atom fun s : Hist X => f s.last) 0 0 T ?base ?ind ?target
  case base =>
    rintro _ ⟨⟨x, hx, rfl⟩, ⟨y, hy, hxy⟩⟩
    have h0 : x 0 = y 0 := (pre_eq_iff.1 (congrFun hxy 0) 0 le_rfl).symm
    refine ⟨rfl, ⟨x, ⟨hx, hA y x h0.symm hy⟩, rfl⟩, ?_⟩
    intro z hz _ k hk1 hk2
    obtain rfl : k = 0 := by omega
    exact hstep z hz 0 hk1 fun k h1 h2 => absurd h2 (by omega)
  case ind =>
    rintro τ - - s ⟨hlen, ⟨x, hx, hsx⟩, hbox⟩ s' ⟨x', hx', hs, hs'⟩
    rw [hlen] at hs hs'
    have hagree : ∀ k ≤ τ, x k = x' k := pre_eq_iff.1 (hsx.symm.trans hs)
    have hxA : x' ∈ A := hA x x' (hagree 0 (Nat.zero_le _)) hx.2
    refine ⟨by rw [hs']; rfl, ⟨x', ⟨hx', hxA⟩, hs'⟩, ?_⟩
    intro z hz hz' k hk1 hk2
    have hzx : ∀ k ≤ τ + 1, x' k = z k := pre_eq_iff.1 (hs'.symm.trans hz')
    have hsz : s = pre z τ := hs.trans (pre_eq_iff.2 fun k hk => hzx k (by omega))
    have hprev : ∀ k, t₀ ≤ k → k ≤ τ → Box z k := hbox z hz hsz
    rcases Nat.lt_or_ge k (τ + 1) with hk | hk
    · exact hprev k hk1 (by omega)
    · obtain rfl : k = τ + 1 := by omega
      exact hstep z hz (τ + 1) hk1 fun k h1 h2 => hprev k h1 (by omega)
  case target =>
    rintro τ - - s ⟨hlen, ⟨x, hx, hsx⟩, hbox⟩
    show 0 ≤ f s.last
    rw [hsx, pre_last]
    rcases Nat.lt_or_ge τ t₀ with hτ | hτ
    · exact hearly x hx τ hτ
    · exact htarget x hx τ hτ (hbox x hx hsx τ hτ le_rfl)
  rintro x ⟨hxM, hxA⟩
  have h := rule ⟨⟨x, hxM, rfl⟩, ⟨x, hxA, rfl⟩⟩
  simp only [Set.mem_ofPred_eq, sat_always, sat_atom] at h
  simp only [mem_lang_t, sat_always, sat_atom]
  intro τ h1 h2
  have := h τ h1 h2
  simpa [hist] using this

end Contracts.Track.Reach.Safe
