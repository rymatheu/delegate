import Contracts.Lift
import Copter.Loop

/-!
# The ArduCopter port as a component over behaviors `ℕ → CX`

The universe `CX` of one tick holds what the `copter` executable reads and writes on that tick
(`Copter/Main.lean`, `Copter.Cli.runStdio`): the parsed input line, an `AHRS.Sample`, and the four
actuator values it prints, `State.actuators` after the tick. Every other quantity of the vehicle
(the whole `Copter.State`) is hidden.

`Copter.loop` is partial (`Option State`: `none` when the switch into Auto fails on an empty
mission) and the executable applies the harness's initial condition `Copter.takeover` with the
first sample before the first tick. `tick` is the total step that `runStdio` performs, with its
`started` flag as part of the hidden state:

* on the first sample, `takeover` and then `loop`; afterwards `loop` alone;
* on `some st'`, the new state is `st'` and the output is `st'.actuators`, as printed;
* on `none` the executable stops with status 1. A behavior over `ℕ` must go on, so here the
  hidden state is kept and the output is four zeros (the motors stopped); every later tick fails
  the same way. With a nonempty mission this branch is never taken (`loop_isSome`), and the
  executable refuses an empty mission before the first tick, so for every run the step is
  exactly `runStdio`'s.

`Mcopter P` is the hidden-state lift of `tick P` from the boot state, in the style of
`Contracts.QuadPlant.MctrlP`. The receptiveness and non-emptiness lemmas of `Contracts.Lift` are
instantiated for it at the end.
-/

namespace Contracts.CopterLift

open Contracts.Lift Copter AP_Math

/-- One tick of the `copter` executable: the sample it reads and the four actuators it writes. -/
-- <<CX>>
structure CX where
  /-- The parsed input line of the tick. -/
  smp : AHRS.Sample
  /-- The actuator values printed for the tick, motor slots 0..3. -/
  act : Vector ftype 4
-- <</CX>>

/-- The hidden state of the executable: the vehicle and whether the first sample has arrived. -/
structure Harness where
  /-- The vehicle object. -/
  st : State
  /-- Whether `takeover` has been applied (`runStdio`'s `started`). -/
  started : Bool

/-- The hidden state before the first sample: the objects as constructed at boot. -/
def Harness.init (P : Parameters) : Harness := ⟨State.init P, false⟩

/-- One tick of `runStdio` on a parsed sample, made total (module docstring). -/
-- <<tick>>
def tick (P : Parameters) (h : Harness) (smp : AHRS.Sample) : Harness × Vector ftype 4 :=
  let st := if h.started then h.st else takeover P h.st smp
  match loop P st smp with
  | some st' => (⟨st', true⟩, st'.actuators)
  | none => (⟨st, true⟩, #v[0.0, 0.0, 0.0, 0.0])
-- <</tick>>

/-- The ArduCopter port with parameters `P`: reads `smp`, writes `act`, hidden `Harness`. -/
-- <<Mcopter>>
def Mcopter (P : Parameters) : Set (ℕ → CX) :=
  liftHidden (·.smp) (·.act) (tick P) (Harness.init P)
-- <</Mcopter>>

/-- The port with the built-in parameters (`Copter.defaults`). -/
def McopterDefaults : Set (ℕ → CX) := Mcopter defaults

theorem mem_Mcopter {P : Parameters} {x : ℕ → CX} :
    x ∈ Mcopter P ↔ ∃ s : ℕ → Harness, s 0 = Harness.init P ∧
      ∀ t, (s (t+1), (x t).act) = tick P (s t) (x t).smp := Iff.rfl

/-! ## The `none` branch is never taken on a nonempty mission -/

/-- With a nonempty mission, `ModeAuto.init` succeeds. -/
theorem enter_auto_isSome {P : Parameters} (hP : P.mission ≠ []) (s : State) :
    ∃ s', enter_auto P s = some s' := by
  have : ModeAuto.mission_present P = true := by
    simp [ModeAuto.mission_present, hP]
  unfold enter_auto ModeAuto.init
  simp [this]

/-- With a nonempty mission, `Copter.loop` never returns `none`. -/
-- <<loop_isSome>>
theorem loop_isSome {P : Parameters} (hP : P.mission ≠ []) (s : State) (smp : AHRS.Sample) :
    ∃ s', loop P s smp = some s' := by
  unfold loop
  dsimp only
  split
  · exact ⟨_, rfl⟩
  · obtain ⟨s', hs'⟩ := enter_auto_isSome hP
      (read_inertia (read_AHRS (motors_output_main P (run_rate_controller_main P
        (ins_update (scheduler_loop s smp.dt_us) smp))) smp))
    rw [hs']
    exact ⟨_, rfl⟩
-- <</loop_isSome>>

/-- With a nonempty mission, `tick` is `runStdio`'s step: the state after the tick is the result
of `loop` and the output is its actuators. -/
theorem tick_of_mission {P : Parameters} (hP : P.mission ≠ []) (h : Harness) (smp : AHRS.Sample) :
    ∃ st', loop P (if h.started then h.st else takeover P h.st smp) smp = some st' ∧
      tick P h smp = (⟨st', true⟩, st'.actuators) := by
  obtain ⟨st', hst'⟩ := loop_isSome hP (if h.started then h.st else takeover P h.st smp) smp
  refine ⟨st', hst', ?_⟩
  unfold tick
  dsimp only
  rw [hst']

/-- The built-in mission is nonempty. -/
theorem defaults_mission_ne : defaults.mission ≠ [] := by
  simp [defaults, defaultMission]

/-! ## Receptiveness and non-emptiness

`Lift.liftHidden_receptive` and `Lift.liftHidden_inter_nonempty`, through the tick type `CX` in
place of the product `AHRS.Sample × Vector ftype 4`. -/

/-- Every input stream extends to a behavior of the port that reads it at every tick. -/
-- <<Mcopter_receptive>>
theorem Mcopter_receptive (P : Parameters) (y : ℕ → AHRS.Sample) :
    ∃ x ∈ Mcopter P, ∀ t, (x t).smp = y t := by
  obtain ⟨x, ⟨s, h0, hs⟩, hxy⟩ := liftHidden_receptive (fun y : AHRS.Sample => y) (tick P)
    (Harness.init P) y
  exact ⟨fun t => ⟨(x t).1, (x t).2⟩, ⟨s, h0, hs⟩, hxy⟩
-- <</Mcopter_receptive>>

/-- Non-vacuity: a nonempty set of behaviors whose membership depends only on the samples meets
the port. -/
-- <<Mcopter_inter_nonempty>>
theorem Mcopter_inter_nonempty (P : Parameters) {A : Set (ℕ → CX)} (hA : A.Nonempty)
    (hdep : ∀ x x' : ℕ → CX, (∀ t, (x t).smp = (x' t).smp) → (x ∈ A ↔ x' ∈ A)) :
    (Mcopter P ∩ A).Nonempty := by
  obtain ⟨a, ha⟩ := hA
  obtain ⟨x, hx, hxy⟩ := Mcopter_receptive P (fun t => (a t).smp)
  exact ⟨x, hx, (hdep x a hxy).2 ha⟩
-- <</Mcopter_inter_nonempty>>

/-- A sample: level, at rest, 10 m above the origin, 2500 µs. -/
def hoverSample : AHRS.Sample :=
  { pos := ⟨0, 0, -10⟩, vel := {}, accel_ef := ⟨0, 0, -GRAVITY_MSS⟩, quat := {}, gyro := {},
    dt_us := 2500 }

/-- The port has a behavior. -/
theorem Mcopter_nonempty (P : Parameters) : (Mcopter P).Nonempty := by
  obtain ⟨x, hx, -⟩ := Mcopter_receptive P (fun _ => hoverSample)
  exact ⟨x, hx⟩

/-- The hidden-state lift is the projection of the visible recurrence over `Harness × CX` with
the boot state fixed (`Lift.liftHidden_eq_proj_liftStep`). -/
theorem Mcopter_eq_proj (P : Parameters) :
    Mcopter P =
      (fun z : ℕ → Harness × CX => fun t => (z t).2) ''
        (liftStep (X := Harness × CX) Prod.fst (fun p => p.2.smp) (fun p => p.2.act) (tick P)
          ∩ {z | (z 0).1 = Harness.init P}) :=
  liftHidden_eq_proj_liftStep _ _ _ _

end Contracts.CopterLift
