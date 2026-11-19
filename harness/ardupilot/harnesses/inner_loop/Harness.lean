import Harness.System
import ardupilot.harnesses.rate.Harness
import ardupilot.modules.mixer.Module

/-! # inner_loop: the rate controller and the motor mixer

One ArduCopter tick of the inner loop (Copter::fast_loop, ArduCopter/Attitude.cpp): the rate
controller runs (`attitude_control->rate_controller_run()`, the system `rate`), then the motors
output (`motors_output()`, the module `mixer`). Both read the same loop time
(`attitude_control->set_dt_s(last_loop_time_s)` and `motors->set_dt_s(last_loop_time_s)`), so
`dt` is one input.

Wires, besides the system's own inputs and parameters (fields of the same names):
* rate's `roll`, `pitch`, `yaw` commands → mixer's `roll`, `pitch`, `yaw` (`_motors.set_roll(..)`);
* mixer's `limit_roll/pitch/yaw` → rate's `limit_roll/pitch/yaw` through `prev`, false at the
  first tick: the rate controller reads `_motors.limit` as the mixer left it on the previous tick;
* mixer's `roll_ff`, `pitch_ff`, `yaw_ff` ← the constant 0. ArduCopter passes
  `get_rate_*_pid().get_ff()` (`_feedforward_scalar` times it for yaw), which is
  `_target * _kff + _target_derivative * _kdff`; the rate_pid module fixes `kff` and `kdff` at 0,
  so with a finite target it is 0.

Not wired: the clocks `now_ms` (rate) and `now_us` (mixer) are separate inputs, although both are
read from the one HAL clock (their relation is arithmetic, which wiring does not do). -/

namespace Ardupilot.Harnesses.InnerLoop

open Harness Harness.Contract.Lang

private def v (n : String) : Expr := .var n
private def axes : List String := ["roll", "pitch", "yaw"]

/-- The mixer inputs that come from wires, not from the system's inputs. -/
private def mixerWired : List String :=
  ["roll", "pitch", "yaw", "roll_ff", "pitch_ff", "yaw_ff", "dt"]

def params : Schema := Ardupilot.Harnesses.Rate.params ++ Ardupilot.Modules.Mixer.params

def input : Schema :=
  Ardupilot.Harnesses.Rate.input.filter (fun f => !f.name.startsWith "limit_") ++
  Ardupilot.Modules.Mixer.input.filter (fun f => !mixerWired.contains f.name)

def output : Schema :=
  (Ardupilot.Modules.Mixer.output.filter fun f => f.name.startsWith "actuator_" ||
    (f.name.startsWith "pwm_" && f.name != "pwm_writes") || f.name.startsWith "limit_" ||
    f.name == "spool_state") ++
  (Ardupilot.Harnesses.Rate.output.filter fun f => axes.contains f.name ||
    f.name.endsWith "_internal_errors") ++
  #[{ name := "mixer_internal_errors", type := .u32, doc := "mixer: internal errors since init" }]

/-- The field fed by the system field of the same name. -/
private def same (s : Schema) (kind : String → Source) : List Wire :=
  s.toList.map fun f => ⟨f.name, kind f.name⟩

def rateChild : Child where
  name := "rate"
  node := .system Ardupilot.Harnesses.Rate.system
  params := same Ardupilot.Harnesses.Rate.params .param
  input := Ardupilot.Harnesses.Rate.input.toList.map fun f =>
    if f.name.startsWith "limit_" then ⟨f.name, .prev "mixer" f.name (.bool false)⟩
    else ⟨f.name, .input f.name⟩

def mixerChild : Child where
  name := "mixer"
  node := .module Ardupilot.Modules.Mixer.module
  params := same Ardupilot.Modules.Mixer.params .param
  input := Ardupilot.Modules.Mixer.input.toList.map fun f =>
    if axes.contains f.name then ⟨f.name, .out "rate" f.name⟩
    else if f.name.endsWith "_ff" then ⟨f.name, .const (.f32 0)⟩
    else ⟨f.name, .input f.name⟩

/-- The children's assumptions on what the system feeds them directly, for a given statement of
the mixer's assumption: all of rate's, and the mixer's except those on wired fields (its
commands clause and `ff_range`); the mixer's `dt_range` is kept as `mixer_dt_range`. -/
def assumeChildrenOf (mixerAssume : List Clause) : List Clause :=
  Ardupilot.Harnesses.Rate.contract.assume ++
  (mixerAssume.filter fun c =>
    !["commands_range", "commands_bounded", "ff_range"].contains c.name).map fun c =>
      if c.name == "dt_range" then { c with name := "mixer_dt_range" } else c

def guarantee : List Clause :=
  Ardupilot.Modules.Mixer.guarantee.filter
    (fun c => ["actuators_in_range", "pwm_in_range"].contains c.name)
  ++ [⟨"rate_no_internal_error", v "roll_internal_errors" =. 0 ∧. v "pitch_internal_errors" =. 0 ∧.
        v "yaw_internal_errors" =. 0⟩,
      ⟨"mixer_no_internal_error", v "mixer_internal_errors" =. 0⟩]

/-- The contract as first stated: the children's assumptions on what the system feeds them (the
mixer's second statement, `contractSecond`), nothing on the commands rate passes to the mixer.
Its campaign (seed 1, 300 x 100,
ardupilot/harnesses/inner_loop/evidence/tested/20261118T155009Z-seed1.json) showed the mixer's
`commands_range` (|roll|, |pitch|, |yaw| ≤ 1) not discharged in 285 of 300 cases. Kept for the
record, not used. -/
def contractAsFirstStated : Contract where
  assume := assumeChildrenOf Ardupilot.Modules.Mixer.contractSecond.assume
  guarantee := guarantee

/-- The second attempt: the P+D limit on and small, so that |command| ≤ kpdmax + kimax ≤ 1
(rate's `*_command_bounded`). Not used: that bound is false (see
`Ardupilot.Harnesses.Rate.commandBoundedAsFirstStated`), and it excludes stock ArduCopter, whose
ATC_RAT_*_PDMX is 0. -/
def assumeCommandsLimited : List Clause :=
  axes.map fun a =>
    ⟨s!"{a}_command_limited", 1.1920929e-7 ≤. v s!"{a}_kpdmax" ∧. v s!"{a}_kpdmax" ≤. 0.5 ∧.
      v s!"{a}_kimax" ≤. 0.49⟩

/-- The second statement, kept for the record (not used). -/
def contractSecond : Contract where
  assume := assumeChildrenOf Ardupilot.Modules.Mixer.contractSecond.assume ++ assumeCommandsLimited
  guarantee := guarantee

/-- IMAX within ArduPilot's documented range, 0 to 1 (@Range of ATC_RAT_RLL/PIT/YAW_IMAX,
AC_AttitudeControl_Multi.cpp:31, 129, 227). With it rate's `*_command_magnitude`,
|command| ≤ 3.5e15 + kimax, gives |command| ≤ 1e16, the mixer's `commands_bounded`. PDMX may
be 0. -/
def assumeImaxDocumented : List Clause :=
  axes.map fun a => ⟨s!"{a}_kimax_documented", v s!"{a}_kimax" ≤. 1⟩

/-- The contract. -/
def contract : Contract where
  assume := assumeChildrenOf Ardupilot.Modules.Mixer.contract.assume ++ assumeImaxDocumented
  guarantee := guarantee

/-- Flight, as the mixer's: armed, interlock on, THROTTLE_UNLIMITED asked for, spool-up block
cleared; both clocks advance about one 400 Hz tick per step. -/
def flight : Regime where
  name := "flight"
  doc := "armed and flying"
  clauses := Ardupilot.Modules.Mixer.flight.clauses
  hints := [.increasing "now_us" 1000000 2400 2600, .increasing "now_ms" 1000 2 3]

/-- The stock vehicle in flight: rate's and the mixer's `stock_flight` parameters and inputs
(the commands are wired, so the mixer's command clause is not part of it). -/
def stockFlight : Regime where
  name := "stock_flight"
  doc := "ArduCopter's default rate gains and MOT_ parameters, flight-like signals, 400 Hz"
  clauses := Ardupilot.Harnesses.Rate.stockParams ++ Ardupilot.Harnesses.Rate.stockSignals ++
    Ardupilot.Modules.Mixer.stockParams ++
    Ardupilot.Modules.Mixer.stockInputs.filter (·.name != "stock_dt")
  hints := flight.hints

/-- The system `inner_loop`. -/
def system : Sys where
  name := "inner_loop"
  doc := "rate controller then motor mixer, the limit flags fed back through prev"
  params := params
  input := input
  output := output
  children := [rateChild, mixerChild]
  outputs := output.toList.map fun f =>
    if f.name == "mixer_internal_errors" then ⟨f.name, .out "mixer" "internal_errors"⟩
    else if axes.contains f.name || f.name.endsWith "_internal_errors" then
      ⟨f.name, .out "rate" f.name⟩
    else ⟨f.name, .out "mixer" f.name⟩
  contract := contract
  regimes := [flight, stockFlight]
  coverage := Ardupilot.Modules.Mixer.coverage

end Ardupilot.Harnesses.InnerLoop
