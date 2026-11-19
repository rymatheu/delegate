import Harness.Module

/-! # est_scenario: a test fixture for the estimator, not ArduPilot code

What a pilot and the vehicle's arming do in the estimator's tracking tests (ardupilot/harnesses/est_loop):
the motors off and the vehicle disarmed until `hover_from_us`, then all four motors at `hover_pwm`
with the vehicle armed and flying, until `hover_until_us`, then off again. The clause language
cannot schedule an input over time (it has no clock of its own and no previous tick), so the
schedule is this module's, run from the plant's `t_us`. It compiles no ArduPilot source
(sources.txt is empty); adapter.cpp is the whole of it. -/

namespace Ardupilot.Modules.EstScenario

open Harness Harness.Contract.Lang

def params : Schema := #[
  { name := "hover_pwm", type := .u32, doc := "PWM of all four motors in the flight phase, us" },
  { name := "hover_from_us", type := .u32, doc := "t_us at which the flight phase starts" },
  { name := "hover_until_us", type := .u32, doc := "t_us at which it ends" }]

def input : Schema := #[
  { name := "t_us", type := .u32,
    doc := "the plant's time (plant_sim's output of the same tick)" }]

private def pwmField (i : Nat) : Field :=
  { name := s!"pwm{i}", type := .u32, init := 1000,
    doc := s!"motor slot {i} PWM for the plant's next tick: hover_pwm in flight, else 1000" }

def output : Schema := #[pwmField 0, pwmField 1, pwmField 2, pwmField 3,
  { name := "armed", type := .bool, doc := "the vehicle armed: in the flight phase" },
  { name := "likely_flying", type := .bool, doc := "the vehicle flying: in the flight phase" }]

private def v (n : String) : Expr := .var n

/-- The phase, away from its two edges by 1000 us: the clause language reads the u32 times as
binary32, which rounds above 2^24 us (up to 256 us below 2^32); the C++ compares them exactly. -/
def surelyFlight : Expr :=
  v "hover_from_us" + 1000 ≤. v "t_us" ∧. v "t_us" + 1000 ≤. v "hover_until_us"

def surelyGround : Expr :=
  v "t_us" + 1000 ≤. v "hover_from_us" ∨. v "hover_until_us" + 1000 ≤. v "t_us"

def contract : Contract where
  assume := [⟨"hover_pwm_range", 1000 ≤. v "hover_pwm" ∧. v "hover_pwm" ≤. 2000⟩]
  guarantee := [
    ⟨"one_phase", (v "armed" ∧. v "likely_flying" ∧. v "pwm0" =. v "hover_pwm" ∧.
        v "pwm1" =. v "hover_pwm" ∧. v "pwm2" =. v "hover_pwm" ∧. v "pwm3" =. v "hover_pwm") ∨.
      (¬. v "armed" ∧. ¬. v "likely_flying" ∧. v "pwm0" =. 1000 ∧. v "pwm1" =. 1000 ∧.
        v "pwm2" =. 1000 ∧. v "pwm3" =. 1000)⟩,
    ⟨"schedule", (¬. surelyFlight ∨. v "armed") ∧. (¬. surelyGround ∨. ¬. v "armed")⟩,
    ⟨"pwm_range", 1000 ≤. v "pwm0" ∧. v "pwm0" ≤. 2000 ∧. 1000 ≤. v "pwm1" ∧. v "pwm1" ≤. 2000 ∧.
        1000 ≤. v "pwm2" ∧. v "pwm2" ≤. 2000 ∧. 1000 ≤. v "pwm3" ∧. v "pwm3" ≤. 2000⟩]

def module : Module where
  name := "est_scenario"
  doc := "test fixture: motors off and disarmed, then a fixed PWM armed, from t_us"
  params := params
  input := input
  output := output
  contract := contract
  exe := "build/modules/est_scenario/est_scenario"
  stack := .ardupilot

end Ardupilot.Modules.EstScenario
