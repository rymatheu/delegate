import Harness.Algebra
import Plant.Step.Sample
import Plant.Step.Period
import Plant.Flow.Motor

/-! # The ODE plant as a harness

The X500 plant of the library `Plant` (an ODE over the reals, the four commands held over each
period, exact flow per period) wrapped as a harness of `Harness.Algebra`, so that it closes a
loop with any controller harness by the loop rule.

* Section 1 adds evidence for a claim proved in Lean (no ledger leaf). It belongs in
  `Harness/Algebra.lean` and is here only because that file is not edited from this one.
* Section 2 is the plant as a set of behaviours, generic in the behaviour type `B`: two
  projections give the commands and the plant state at each tick.
* Section 3 is the plant's step contract and the theorem that the plant meets it. Every clause is
  glued from a theorem of `Plant`; nothing is re-analyzed.
* Section 4 is the plant harness: valid, backed under every policy, faithful under every policy.
* Section 5 closes a loop around the plant: plant first, controller second within a tick. The
  closed loop is backed exactly when the controller is.

Nothing is left unproved and no axiom is added; `check.sh` prints the axioms used. -/

namespace Harness.Algebra

/-! ## 1. Evidence for a Lean theorem (to be moved into Harness/Algebra.lean) -/

variable {ρ B : Type}

/-- Evidence for a claim proved in Lean: derived from the empty conjunction, so it has no leaf
and needs no ledger record. -/
def Ev.ofProof {P : Prop} (hP : P) : Ev ρ P :=
  .derive (.all (n := 0) (Q := fun _ => True) (fun i => i.elim0)) (fun _ => hP)

/-- Proved evidence is supported under every policy, the empty one included. -/
theorem Ev.ofProof_supported {P : Prop} (hP : P) (T : ρ → Prop) :
    (Ev.ofProof (ρ := ρ) hP).supported T := by
  intro i
  exact i.elim0

/-- Proved evidence is faithful under every policy: it has no record to be false. -/
theorem Ev.ofProof_faithful {P : Prop} (hP : P) (T : ρ → Prop) :
    (Ev.ofProof (ρ := ρ) hP).faithful T := by
  intro i
  exact i.elim0

-- `Harness.Algebra.Harness` is the algebra's own nesting (`Harness/Algebra.lean`, section 6).
set_option linter.dupNamespace false

/-- A harness whose claim is a Lean theorem. -/
def Harness.ofProof (M : B → Prop) (C : Contract B) (h : M ⊨ C) : Harness ρ B :=
  ⟨M, C, Ev.ofProof h⟩

/-- A proved harness is backed under every policy. -/
theorem Harness.backed_ofProof (M : B → Prop) (C : Contract B) (h : M ⊨ C) (T : ρ → Prop) :
    (Harness.ofProof (ρ := ρ) M C h).Backed T :=
  Ev.ofProof_supported h T

/-- A proved harness is faithful under every policy. -/
theorem Harness.faithful_ofProof (M : B → Prop) (C : Contract B) (h : M ⊨ C) (T : ρ → Prop) :
    (Harness.ofProof (ρ := ρ) M C h).Faithful T :=
  Ev.ofProof_faithful h T

end Harness.Algebra

namespace Harness.Formal

open Harness.Algebra
open Plant (PState IsRun nextR ThrustRange qnormSq vI)

variable {ρ B : Type}

/-! ## 2. The plant as a set of behaviours -/

/-- **The plant.** `cmd b t` are the four motor commands held over the period after tick `t`;
`st b t` is the plant state at tick `t`. A behaviour is one of the plant's when its states are
a run of the sampled ODE under its commands. Generic in `B`, so the plant sits in any closed-loop
behaviour universe next to other components. -/
def plantImpl (cmd : B → ℕ → Fin 4 → ℝ) (st : B → ℕ → PState) : B → Prop :=
  fun b => IsRun (st b) (cmd b)

/-! ## 3. The step contract -/

/-- The plant's initial condition: a unit attitude quaternion and the four lagged thrusts in
`[0, 1]`. -/
def PlantInit (s : PState) : Prop := qnormSq s.x = 1 ∧ ThrustRange s.x

/-- One period of the plant, exactly: `s'` holds the command `u`, and its rigid-body state is the
endpoint of the ODE solution from `s` over the period `h` with `u` held. -/
def FlowInto (s s' : PState) (u : Fin 4 → ℝ) : Prop :=
  s'.held = u ∧ ∃ γ : ℝ → Plant.X, γ 0 = s.x ∧ γ Plant.h = s'.x ∧
    ∀ τ ∈ Set.Icc 0 Plant.h, HasDerivAt γ (Plant.vf (γ τ) u) τ

/-- The plant's guarantee at tick `t`. It mentions the states up to `t` and the commands before
`t` only: the plant, scheduled first within a tick, produces the state at `t` from the period
that ended at `t`. -/
structure PlantG (cmd : B → ℕ → Fin 4 → ℝ) (st : B → ℕ → PState) (b : B) (t : ℕ) : Prop where
  /-- The attitude quaternion has unit norm. Backed by `Plant.run_qnormSq`. -/
  quat_unit : qnormSq (st b t).x = 1
  /-- The lagged thrusts are in `[0, 1]`. Backed by `Plant.step_thrustRange`. -/
  thrust_range : ThrustRange (st b t).x
  /-- The state at `t` is the exact flow from the state at `t - 1` under the command at `t - 1`.
  Backed by `Plant.run_flow`. -/
  flow : ∀ s, t = s + 1 → FlowInto (st b s) (st b t) (cmd b s)
  /-- Over the period that ended at `t`, each velocity component moved by at most
  `(g + amax) h`. Backed by `Plant.step_v_sub_le`. -/
  vel_step : ∀ s, t = s + 1 → ∀ j : Fin 3,
    |(st b t).x (vI j) - (st b s).x (vI j)| ≤ (Plant.grav + Plant.amax) * Plant.h

/-- **The plant's step contract.** The assumption at tick `t` is the initial condition at tick 0
and nothing at later ticks. It mentions no command at all: the plant clips its commands to
`[0, 1]`, so no command range is needed. The initial condition sits in the plant's own
assumption, not in the environment's `e`, so that the plant harness is valid on its own; in a
closed loop the environment discharges it at tick 0 (`plantA_of_init`). -/
def plantStep (cmd : B → ℕ → Fin 4 → ℝ) (st : B → ℕ → PState) : Step B where
  a := fun b t => t = 0 → PlantInit (st b 0)
  g := PlantG cmd st

/-- The thrusts of a run stay in range when they start in range: `Plant.step_thrustRange`,
period by period. -/
theorem run_thrustRange {s : ℕ → PState} {u : ℕ → Fin 4 → ℝ} (hs : IsRun s u)
    (h0 : ThrustRange (s 0).x) (t : ℕ) : ThrustRange (s t).x := by
  induction t with
  | zero => exact h0
  | succ n ih =>
    rw [hs n]
    exact Plant.step_thrustRange ih (u n)

/-- **The plant meets its step contract** over runs. -/
theorem plant_implements (cmd : B → ℕ → Fin 4 → ℝ) (st : B → ℕ → PState) :
    plantImpl cmd st ⊨ (plantStep cmd st).always := by
  intro b hb _ t ha
  have h0 : PlantInit (st b 0) := ha 0 (Nat.zero_le t) rfl
  have hq : ∀ n, qnormSq (st b n).x = 1 := fun n => (Plant.run_qnormSq hb n).trans h0.1
  have hf : ∀ n, ThrustRange (st b n).x := run_thrustRange hb h0.2
  refine ⟨hq t, hf t, ?_, ?_⟩
  · intro s hs
    subst hs
    refine ⟨?_, Plant.run_flow hb s⟩
    rw [hb s]
    rfl
  · intro s hs j
    subst hs
    rw [hb s]
    exact Plant.step_v_sub_le (hq s) (hf s) (cmd b s) j

/-! ## 4. The plant harness -/

/-- **The plant harness**: the ODE plant, its step contract over runs, and evidence that is a Lean
proof with no ledger leaf. -/
def plantHarness (cmd : B → ℕ → Fin 4 → ℝ) (st : B → ℕ → PState) : Harness ρ B :=
  Harness.ofProof (plantImpl cmd st) (plantStep cmd st).always (plant_implements cmd st)

/-- The plant harness is valid. -/
theorem plantHarness_valid (cmd : B → ℕ → Fin 4 → ℝ) (st : B → ℕ → PState) :
    (plantHarness (ρ := ρ) cmd st).Valid :=
  plant_implements cmd st

/-- The plant harness is backed under every policy. -/
theorem plantHarness_backed (cmd : B → ℕ → Fin 4 → ℝ) (st : B → ℕ → PState) (T : ρ → Prop) :
    (plantHarness cmd st).Backed T :=
  Harness.backed_ofProof _ _ _ T

/-- The plant harness is backed under the empty policy: it trusts no record. -/
theorem plantHarness_backed_empty (cmd : B → ℕ → Fin 4 → ℝ) (st : B → ℕ → PState) :
    (plantHarness (ρ := ρ) cmd st).Backed (fun _ => False) :=
  plantHarness_backed cmd st _

/-- The plant harness is faithful under every policy. -/
theorem plantHarness_faithful (cmd : B → ℕ → Fin 4 → ℝ) (st : B → ℕ → PState) (T : ρ → Prop) :
    (plantHarness cmd st).Faithful T :=
  Harness.faithful_ofProof _ _ _ T

/-! ## 5. Closing a loop around the plant -/

/-- Two harnesses as the schedule of `Harness.loop`: `H₀` first, `H₁` second. -/
def pairH (H₀ H₁ : Harness ρ B) : Nat → Harness ρ B
  | 0 => H₀
  | _ + 1 => H₁

/-- Two step contracts as the schedule of `Harness.loop`. -/
def pairS (S₀ S₁ : Step B) : Nat → Step B
  | 0 => S₀
  | _ + 1 => S₁

/-- The closed loop's contract: the plant's and the controller's guarantees at every tick up to
which the environment's assumption `e` has held. -/
def loopContract (cmd : B → ℕ → Fin 4 → ℝ) (st : B → ℕ → PState) (Sc : Step B)
    (e : B → ℕ → Prop) : Contract B :=
  (Step.mk e (fun b t => (plantStep cmd st).g b t ∧ Sc.g b t)).always

/-- **Close a loop around the plant.** `Hc` is a controller harness whose contract refines the
step contract `Sc`. Within a tick the plant runs first, then the controller. `hAp`: the plant's
assumption at `t` follows from `e` up to `t` and both guarantees before `t`. `hAc`: the
controller's assumption at `t` follows from `e` up to `t` and the plant's guarantee at `t`. Built
with `Harness.loop` (`n = 2`), then `Harness.refine` to the contract `loopContract`. -/
def closeLoop (cmd : B → ℕ → Fin 4 → ℝ) (st : B → ℕ → PState) (Hc : Harness ρ B) (Sc : Step B)
    (e : B → ℕ → Prop) (hCc : Hc.contract ⪯ Sc.always)
    (hAp : ∀ b t, (∀ s, s ≤ t → e b s) → (∀ s, s < t → (plantStep cmd st).g b s ∧ Sc.g b s) →
      (plantStep cmd st).a b t)
    (hAc : ∀ b t, (∀ s, s ≤ t → e b s) → (plantStep cmd st).g b t → Sc.a b t) :
    Harness ρ B :=
  Harness.refine
    (Harness.loop 2 (pairH (plantHarness cmd st) Hc) (pairS (plantStep cmd st) Sc) e
      (fun i hi => match i, hi with
        | 0, _ => refines_refl _
        | 1, _ => hCc)
      (fun b t he i hi hcur hprev => match i, hi with
        | 0, _ => hAp b t he fun s hs => ⟨hprev 0 (by decide) s hs, hprev 1 (by decide) s hs⟩
        | 1, _ => hAc b t he (hcur 0 (by decide))))
    (loopContract cmd st Sc e)
    ⟨fun _ _ => trivial,
      fun _ hs _ t he => ⟨hs trivial t he 0 (by decide), hs trivial t he 1 (by decide)⟩⟩

/-- The environment discharges the plant's assumption when it sets the initial condition at
tick 0. -/
theorem plantA_of_init (cmd : B → ℕ → Fin 4 → ℝ) (st : B → ℕ → PState) (Sc : Step B)
    (e : B → ℕ → Prop) (hinit : ∀ b, e b 0 → PlantInit (st b 0)) :
    ∀ b t, (∀ s, s ≤ t → e b s) → (∀ s, s < t → (plantStep cmd st).g b s ∧ Sc.g b s) →
      (plantStep cmd st).a b t :=
  fun b t he _ _ => hinit b (he 0 (Nat.zero_le t))

section closeLoop

variable (cmd : B → ℕ → Fin 4 → ℝ) (st : B → ℕ → PState) (Hc : Harness ρ B) (Sc : Step B)
  (e : B → ℕ → Prop) (hCc : Hc.contract ⪯ Sc.always)
  (hAp : ∀ b t, (∀ s, s ≤ t → e b s) → (∀ s, s < t → (plantStep cmd st).g b s ∧ Sc.g b s) →
    (plantStep cmd st).a b t)
  (hAc : ∀ b t, (∀ s, s ≤ t → e b s) → (plantStep cmd st).g b t → Sc.a b t)

/-- The closed loop's contract is `loopContract`: the `always` of `e` and both guarantees. -/
theorem closeLoop_contract :
    (closeLoop cmd st Hc Sc e hCc hAp hAc).contract =
      (Step.mk e (fun b t => (plantStep cmd st).g b t ∧ Sc.g b t)).always :=
  rfl

/-- The closed loop's behaviours are those of the plant and of the controller. -/
theorem closeLoop_impl (b : B) :
    (closeLoop cmd st Hc Sc e hCc hAp hAc).impl b ↔ plantImpl cmd st b ∧ Hc.impl b :=
  ⟨fun h => ⟨h 0 (by decide), h 1 (by decide)⟩,
    fun h i hi => match i, hi with
      | 0, _ => h.1
      | 1, _ => h.2⟩

/-- **Closing the loop with the ODE plant adds nothing to what has to be trusted**: the closed
loop is backed under a policy exactly when the controller is. -/
theorem closeLoop_backed (T : ρ → Prop) :
    (closeLoop cmd st Hc Sc e hCc hAp hAc).Backed T ↔ Hc.Backed T :=
  ⟨fun h => h ⟨1, by decide⟩,
    fun h i => match i with
      | ⟨0, _⟩ => plantHarness_backed cmd st T
      | ⟨1, _⟩ => h⟩

/-- The closed loop is faithful under a policy exactly when the controller is. -/
theorem closeLoop_faithful (T : ρ → Prop) :
    (closeLoop cmd st Hc Sc e hCc hAp hAc).Faithful T ↔ Hc.Faithful T :=
  ⟨fun h => h ⟨1, by decide⟩,
    fun h i => match i with
      | ⟨0, _⟩ => plantHarness_faithful cmd st T
      | ⟨1, _⟩ => h⟩

/-- Soundness of the closed loop: under a policy whose accepted records are true, a backed
controller makes the closed loop valid. -/
theorem closeLoop_valid {T : ρ → Prop} (hf : Hc.Faithful T) (hb : Hc.Backed T) :
    (closeLoop cmd st Hc Sc e hCc hAp hAc).Valid :=
  Harness.sound _ ((closeLoop_faithful cmd st Hc Sc e hCc hAp hAc T).2 hf)
    ((closeLoop_backed cmd st Hc Sc e hCc hAp hAc T).2 hb)

end closeLoop

end Harness.Formal
