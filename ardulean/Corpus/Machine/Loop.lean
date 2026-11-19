import ArduLean.Runtime.Memory

/-!
# Loops of the translation (`for i in [a:b]`, `for _ in PMem.loopFuel`)

The translation writes a counted C loop as Lean's `for i in [a:b] do …`, which elaborates to `forIn` over a
`Std.Legacy.Range` in `PMem.M`, and every other loop as `for _ in PMem.loopFuel do …`, which is `PMem.Fuel.loop` (at
most `n` iterations; on running out the sticky flag `fuelOut` is set). This file gives, for both, an unrolling law and
an invariant rule. The invariant rules take the early exit (`ForInStep.done`, the translation of `break` and of
`return` inside the loop) into account: a step either yields a state of the invariant `I` or ends the loop in a state
of the exit condition `Q`. No ArduPilot function appears here.
-/

namespace Corpus.Loop

/-- What one iteration must establish: `I` when the loop goes on (`yield`), `Q` when it ends (`done`). -/
def StepOK {β : Type} (I Q : β → PMem.Mem → Prop) : ForInStep β → PMem.Mem → Prop
  | .yield b, s => I b s
  | .done b, s => Q b s

@[simp] theorem stepOK_yield {β : Type} (I Q : β → PMem.Mem → Prop) (b : β) (s : PMem.Mem) :
    StepOK I Q (.yield b) s = I b s := rfl

@[simp] theorem stepOK_done {β : Type} (I Q : β → PMem.Mem → Prop) (b : β) (s : PMem.Mem) :
    StepOK I Q (.done b) s = Q b s := rfl

/-! ## Counted loops -/

/-- A counted loop is the loop over the list of its indices. -/
theorem forIn_range {β : Type} (a b : Nat) (init : β) (f : Nat → β → PMem.M (ForInStep β)) :
    forIn (m := PMem.M) [a:b] init f = forIn (List.range' a (b - a)) init f := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simp [Std.Legacy.Range.size]

/-- Unrolling: `for i in [0:1]`. -/
@[simp] theorem forIn_range_0_1 {β : Type} (init : β) (f : Nat → β → PMem.M (ForInStep β)) :
    forIn (m := PMem.M) [0:1] init f = forIn [0] init f := by
  rw [forIn_range]; rfl

/-- Unrolling: `for i in [0:2]`. -/
@[simp] theorem forIn_range_0_2 {β : Type} (init : β) (f : Nat → β → PMem.M (ForInStep β)) :
    forIn (m := PMem.M) [0:2] init f = forIn [0, 1] init f := by
  rw [forIn_range]; rfl

/-- Unrolling: `for i in [0:3]`. -/
@[simp] theorem forIn_range_0_3 {β : Type} (init : β) (f : Nat → β → PMem.M (ForInStep β)) :
    forIn (m := PMem.M) [0:3] init f = forIn [0, 1, 2] init f := by
  rw [forIn_range]; rfl

/-- Unrolling: `for i in [0:4]`. -/
@[simp] theorem forIn_range_0_4 {β : Type} (init : β) (f : Nat → β → PMem.M (ForInStep β)) :
    forIn (m := PMem.M) [0:4] init f = forIn [0, 1, 2, 3] init f := by
  rw [forIn_range]; rfl

/-- One iteration of a loop over a list, through `StateT.run`. -/
theorem forIn_cons_run {β : Type} (i : Nat) (l : List Nat) (init : β) (f : Nat → β → PMem.M (ForInStep β))
    (s : PMem.Mem) :
    (forIn (i :: l) init f).run s =
      match (f i init).run s with
      | (.done b, s') => (b, s')
      | (.yield b, s') => (forIn l b f).run s' := by
  rw [List.forIn_cons]
  simp only [StateT.run, bind, StateT.bind]
  rcases f i init s with ⟨⟨b⟩ | ⟨b⟩, s'⟩ <;> rfl

theorem forIn_nil_run {β : Type} (init : β) (f : Nat → β → PMem.M (ForInStep β)) (s : PMem.Mem) :
    (forIn ([] : List Nat) init f).run s = (init, s) := rfl

/-- Invariant rule for a loop over a list: if `I` holds at entry, each iteration from an `I` state yields an `I` state
or ends in a `Q` state, and `I` at the normal exit implies `Q`, then `Q` holds after the loop. -/
theorem forIn_list_inv {β : Type} (I Q : β → PMem.Mem → Prop) (f : Nat → β → PMem.M (ForInStep β)) :
    ∀ (l : List Nat), (∀ i ∈ l, ∀ b s, I b s → StepOK I Q ((f i b).run s).1 ((f i b).run s).2) →
      (∀ b s, I b s → Q b s) →
      ∀ (init : β) (s : PMem.Mem), I init s → Q ((forIn l init f).run s).1 ((forIn l init f).run s).2
  | [], _, hexit, init, s, h0 => by rw [forIn_nil_run]; exact hexit _ _ h0
  | i :: l, hstep, hexit, init, s, h0 => by
    rw [forIn_cons_run]
    have hi := hstep i (List.mem_cons_self) init s h0
    revert hi
    rcases (f i init).run s with ⟨⟨b⟩ | ⟨b⟩, s'⟩
    · intro hi; exact hi
    · intro hi
      exact forIn_list_inv I Q f l (fun j hj => hstep j (List.mem_cons_of_mem _ hj)) hexit b s' hi

/-- Invariant rule for `for i in [a:b]` (step 1): each iteration may use `a ≤ i < b`. -/
theorem forIn_range_inv {β : Type} (I Q : β → PMem.Mem → Prop) (f : Nat → β → PMem.M (ForInStep β)) (a b : Nat)
    (hstep : ∀ i, a ≤ i → i < b → ∀ c s, I c s → StepOK I Q ((f i c).run s).1 ((f i c).run s).2)
    (hexit : ∀ c s, I c s → Q c s) (init : β) (s : PMem.Mem) (h0 : I init s) :
    Q ((forIn (m := PMem.M) [a:b] init f).run s).1 ((forIn (m := PMem.M) [a:b] init f).run s).2 := by
  rw [forIn_range]
  refine forIn_list_inv I Q f _ ?_ hexit init s h0
  intro i hi
  rw [List.mem_range'_1] at hi
  exact hstep i hi.1 (by omega)

/-- A loop whose every iteration leaves the state unchanged leaves it unchanged. -/
theorem forIn_range_state {β : Type} (f : Nat → β → PMem.M (ForInStep β)) (a b : Nat)
    (hstep : ∀ i c s, ((f i c).run s).2 = s) (init : β) (s : PMem.Mem) :
    ((forIn (m := PMem.M) [a:b] init f).run s).2 = s :=
  forIn_range_inv (fun _ s' => s' = s) (fun _ s' => s' = s) f a b
    (fun i _ _ c s' h => by
      have e := hstep i c s'
      rcases hr : (f i c).run s' with ⟨⟨_⟩ | ⟨_⟩, s''⟩ <;> rw [hr] at e <;> exact e.trans h)
    (fun _ _ h => h) init s rfl

/-! ## Fuel loops (`PMem.Fuel.loop`, `PMem.loopFuel`) -/

/-- The fuel loop's two cases, through `StateT.run`: out of fuel, the flag is set; else one iteration. -/
theorem fuel_loop_zero_run {β : Type} (f : Unit → β → PMem.M (ForInStep β)) (b : β) (s : PMem.Mem) :
    (PMem.Fuel.loop f 0 b).run s = (b, { s with fuelOut := true }) := rfl

theorem fuel_loop_succ_run {β : Type} (f : Unit → β → PMem.M (ForInStep β)) (n : Nat) (b : β) (s : PMem.Mem) :
    (PMem.Fuel.loop f (n + 1) b).run s =
      match (f () b).run s with
      | (.done b', s') => (b', s')
      | (.yield b', s') => (PMem.Fuel.loop f n b').run s' := by
  simp only [PMem.Fuel.loop, StateT.run, bind, StateT.bind]
  rcases f () b s with ⟨⟨b'⟩ | ⟨b'⟩, s'⟩ <;> rfl

/-- Invariant rule for the fuel loop: if `I` holds at entry and each iteration from an `I` state yields an `I` state
or ends in a `Q` state, then after the loop either `Q` holds, or the fuel ran out: the flag `fuelOut` is set and the
state is an `I` state with the flag set. -/
theorem fuel_loop_inv {β : Type} (I Q : β → PMem.Mem → Prop) (f : Unit → β → PMem.M (ForInStep β))
    (hstep : ∀ b s, I b s → StepOK I Q ((f () b).run s).1 ((f () b).run s).2) :
    ∀ (n : Nat) (b : β) (s : PMem.Mem), I b s →
      Q ((PMem.Fuel.loop f n b).run s).1 ((PMem.Fuel.loop f n b).run s).2 ∨
        (((PMem.Fuel.loop f n b).run s).2.fuelOut = true ∧
          ∃ s₀, I ((PMem.Fuel.loop f n b).run s).1 s₀ ∧ ((PMem.Fuel.loop f n b).run s).2 = { s₀ with fuelOut := true })
  | 0, b, s, h0 => by
    rw [fuel_loop_zero_run]
    exact Or.inr ⟨rfl, s, h0, rfl⟩
  | n + 1, b, s, h0 => by
    rw [fuel_loop_succ_run]
    have hi := hstep b s h0
    revert hi
    rcases (f () b).run s with ⟨⟨b'⟩ | ⟨b'⟩, s'⟩
    · intro hi; exact Or.inl hi
    · intro hi; exact fuel_loop_inv I Q f hstep n b' s' hi

/-- The same rule for the translation's `for _ in PMem.loopFuel do …`. -/
theorem loopFuel_inv {β : Type} (I Q : β → PMem.Mem → Prop) (f : Unit → β → PMem.M (ForInStep β))
    (hstep : ∀ b s, I b s → StepOK I Q ((f () b).run s).1 ((f () b).run s).2) (init : β) (s : PMem.Mem)
    (h0 : I init s) :
    Q ((forIn PMem.loopFuel init f).run s).1 ((forIn PMem.loopFuel init f).run s).2 ∨
      (((forIn PMem.loopFuel init f).run s).2.fuelOut = true ∧
        ∃ s₀, I ((forIn PMem.loopFuel init f).run s).1 s₀ ∧
          ((forIn PMem.loopFuel init f).run s).2 = { s₀ with fuelOut := true }) :=
  fuel_loop_inv I Q f hstep _ init s h0

/-- Corollary: a fuel loop that ends with the flag `fuelOut` clear, entered with the flag clear, ended in a `Q`
state. -/
theorem loopFuel_of_fuelOut_false {β : Type} (I Q : β → PMem.Mem → Prop) (f : Unit → β → PMem.M (ForInStep β))
    (hstep : ∀ b s, I b s → StepOK I Q ((f () b).run s).1 ((f () b).run s).2) (init : β) (s : PMem.Mem)
    (h0 : I init s) (hf : ((forIn PMem.loopFuel init f).run s).2.fuelOut = false) :
    Q ((forIn PMem.loopFuel init f).run s).1 ((forIn PMem.loopFuel init f).run s).2 := by
  rcases loopFuel_inv I Q f hstep init s h0 with h | ⟨h, _⟩
  · exact h
  · rw [hf] at h; exact absurd h (by decide)

end Corpus.Loop
