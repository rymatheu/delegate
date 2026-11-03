import Contracts.STL

/-!
# Lifts over behaviours `ℕ → X`

A behaviour is a trajectory `ℕ → X` over
a universe `X` whose fields are the system's signals, and a lift names the fields a function reads
and writes by selectors `X → I` and `X → O`. Every other field is left free, so components over the
same universe compose by intersection.

`liftStep` is the lift of a module with a visible state, an input port and an output port: the
state of the next tick and the output of this tick are produced together from the state and the
input of this tick. `initOn` pulls a formula over a state type `Y` back to behaviours over `X`
through a selector `X → Y`.
-/

namespace Contracts.Lift

variable {X : Type}

/-- The behaviours on which output `out` is the memoryless function `f` of input `inp` at every tick. -/
-- <<liftStatic>>
def liftStatic {I O : Type} (inp : X → I) (out : X → O) (f : I → O) : Set (ℕ → X) :=
  {x | ∀ t, out (x t) = f (inp (x t))}
-- <</liftStatic>>

/-- The behaviours on which the visible state `st` follows the recurrence `f` driven by `inp`. -/
-- <<liftDyn>>
def liftDyn {S I : Type} (st : X → S) (inp : X → I) (f : S → I → S) : Set (ℕ → X) :=
  {x | ∀ t, st (x (t+1)) = f (st (x t)) (inp (x t))}
-- <</liftDyn>>

/-- The behaviours on which some hidden state sequence from `s₀` drives the step `f` that produces
`out` from `inp`. -/
-- <<liftHidden>>
def liftHidden {S I O : Type} (inp : X → I) (out : X → O) (f : S → I → S × O) (s₀ : S) :
    Set (ℕ → X) :=
  {x | ∃ s : ℕ → S, s 0 = s₀ ∧ ∀ t, (s (t+1), out (x t)) = f (s t) (inp (x t))}
-- <</liftHidden>>

/-- The behaviours on which the visible state `st` and the output `out` follow the step `f` driven
by `inp`: the next state and the current output are `f` of the current state and input. -/
-- <<liftStep>>
def liftStep {S I O : Type} (st : X → S) (inp : X → I) (out : X → O) (f : S → I → S × O) :
    Set (ℕ → X) :=
  {x | ∀ t, (st (x (t+1)), out (x t)) = f (st (x t)) (inp (x t))}
-- <</liftStep>>

theorem mem_liftStatic {I O : Type} {inp : X → I} {out : X → O} {f : I → O} {x : ℕ → X} :
    x ∈ liftStatic inp out f ↔ ∀ t, out (x t) = f (inp (x t)) := Iff.rfl

theorem mem_liftDyn {S I : Type} {st : X → S} {inp : X → I} {f : S → I → S} {x : ℕ → X} :
    x ∈ liftDyn st inp f ↔ ∀ t, st (x (t+1)) = f (st (x t)) (inp (x t)) := Iff.rfl

theorem mem_liftStep {S I O : Type} {st : X → S} {inp : X → I} {out : X → O}
    {f : S → I → S × O} {x : ℕ → X} :
    x ∈ liftStep st inp out f ↔ ∀ t, (st (x (t+1)), out (x t)) = f (st (x t)) (inp (x t)) :=
  Iff.rfl

/-- A visible-state lift is a dynamic lift of the state together with a static lift of the output. -/
theorem liftStep_eq {S I O : Type} (st : X → S) (inp : X → I) (out : X → O) (f : S → I → S × O) :
    liftStep st inp out f =
      liftDyn st inp (fun s i => (f s i).1) ∩
        liftStatic (fun x => (st x, inp x)) out (fun si => (f si.1 si.2).2) := by
  ext x
  constructor
  · intro h
    exact ⟨fun t => (Prod.mk.inj (h t)).1, fun t => (Prod.mk.inj (h t)).2⟩
  · rintro ⟨hd, ho⟩ t
    exact Prod.ext (hd t) (ho t)

/-- The behaviours over `X` whose image under `sel` satisfies `φ` at every index. -/
-- <<langOn>>
def langOn {Y : Type} (sel : X → Y) (φ : STL.Formula Y) : Set (ℕ → X) :=
  {x | (fun t => sel (x t)) ∈ STL.lang φ}
-- <</langOn>>

/-- The behaviours over `X` whose image under `sel` satisfies `φ` at index `0`. -/
-- <<initOn>>
def initOn {Y : Type} (sel : X → Y) (φ : STL.Formula Y) : Set (ℕ → X) :=
  {x | (fun t => sel (x t)) ∈ STL.init φ}
-- <</initOn>>

theorem mem_initOn {Y : Type} {sel : X → Y} {φ : STL.Formula Y} {x : ℕ → X} :
    x ∈ initOn sel φ ↔ STL.sat (fun t => sel (x t)) 0 φ := Iff.rfl

/-! ### Receptiveness and the hidden-state projection

`liftHidden_receptive` and `liftHidden_eq_proj` in the selector form. -/

/-- The state sequence that a step function produces from an initial state and an input stream. -/
-- <<runState>>
def runState {S I O : Type} (f : S → I → S × O) (s₀ : S) (i : ℕ → I) : ℕ → S
  | 0 => s₀
  | t+1 => (f (runState f s₀ i t) (i t)).1
-- <</runState>>

/-- A total step function is receptive: over a tick type `Y × O` whose `Y` field feeds the input
and whose `O` field is the output, every input stream `y` extends to a behaviour of the hidden-state
lift that agrees with `y` on the `Y` field at every tick. -/
-- <<liftHidden_receptive>>
theorem liftHidden_receptive {Y S I O : Type} (inp : Y → I) (f : S → I → S × O) (s₀ : S)
    (y : ℕ → Y) :
    ∃ x ∈ liftHidden (fun p : Y × O => inp p.1) Prod.snd f s₀, ∀ t, (x t).1 = y t :=
  ⟨fun t => (y t, (f (runState f s₀ (fun t => inp (y t)) t) (inp (y t))).2),
    ⟨runState f s₀ (fun t => inp (y t)), rfl, fun _ => rfl⟩, fun _ => rfl⟩
-- <</liftHidden_receptive>>

/-- Non-vacuity: a nonempty set of behaviours over `Y × O` whose membership depends only on the
`Y` field meets the hidden-state lift. -/
-- <<liftHidden_inter_nonempty>>
theorem liftHidden_inter_nonempty {Y S I O : Type} (inp : Y → I) (f : S → I → S × O) (s₀ : S)
    {A : Set (ℕ → Y × O)} (hA : A.Nonempty)
    (hdep : ∀ x x' : ℕ → Y × O, (∀ t, (x t).1 = (x' t).1) → (x ∈ A ↔ x' ∈ A)) :
    (liftHidden (fun p : Y × O => inp p.1) Prod.snd f s₀ ∩ A).Nonempty := by
  obtain ⟨a, ha⟩ := hA
  obtain ⟨x, hx, hxy⟩ := liftHidden_receptive inp f s₀ (fun t => (a t).1)
  exact ⟨x, hx, (hdep x a hxy).2 ha⟩
-- <</liftHidden_inter_nonempty>>

/-- A hidden-state lift is the projection, away from the state field, of the visible recurrence
over the tick type `S × X` together with its initial condition and output equation. The projection
forgets the state field pointwise, `z ↦ fun t => (z t).2`. -/
-- <<liftHidden_eq_proj>>
theorem liftHidden_eq_proj {S I O : Type} (inp : X → I) (out : X → O) (f : S → I → S × O)
    (s₀ : S) :
    liftHidden inp out f s₀ =
      (fun z : ℕ → S × X => fun t => (z t).2) ''
        (liftDyn (X := S × X) Prod.fst (fun p => inp p.2) (fun s i => (f s i).1)
          ∩ {z | (z 0).1 = s₀}
          ∩ liftStatic (fun p : S × X => (p.1, inp p.2)) (fun p => out p.2)
              (fun si => (f si.1 si.2).2)) := by
  ext x
  constructor
  · rintro ⟨s, h0, hs⟩
    refine ⟨fun t => (s t, x t), ⟨⟨fun t => ?_, h0⟩, fun t => ?_⟩, rfl⟩
    · exact (Prod.mk.inj (hs t)).1
    · exact (Prod.mk.inj (hs t)).2
  · rintro ⟨z, ⟨⟨hd, h0⟩, ho⟩, rfl⟩
    exact ⟨fun t => (z t).1, h0, fun t => Prod.ext (hd t) (ho t)⟩
-- <</liftHidden_eq_proj>>

/-- The same projection stated through `liftStep`: a hidden-state lift is a visible-state lift
over `S × X` with the initial state fixed, with the state field forgotten. -/
theorem liftHidden_eq_proj_liftStep {S I O : Type} (inp : X → I) (out : X → O)
    (f : S → I → S × O) (s₀ : S) :
    liftHidden inp out f s₀ =
      (fun z : ℕ → S × X => fun t => (z t).2) ''
        (liftStep (X := S × X) Prod.fst (fun p => inp p.2) (fun p => out p.2) f
          ∩ {z | (z 0).1 = s₀}) := by
  rw [liftHidden_eq_proj, liftStep_eq]
  congr 1
  ext z
  simp only [Set.mem_inter_iff]
  tauto

end Contracts.Lift
