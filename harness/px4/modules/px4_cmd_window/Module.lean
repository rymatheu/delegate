import px4.modules.px4_navigator.Ports

/-! # px4_cmd_window: an observer of the vehicle_command traffic

Not PX4 code: a sliding sum (adapter.cpp) of `vehicle_command_count` over the last 400 ticks (1 s
at 400 Hz), this tick included, as `vehicle_command_last_400_ticks`. It exists because the
contract language reads one tick, while what navigator needs of its command traffic is a bound per
pass window (px4_navigator's `command_window`); in a composite it runs after the module that
publishes vehicle_command and before the ones that read it, so its output is a same-tick input of
theirs. Its input field is the subscribers' generated `vehicle_command_count` (the schema is taken
from px4_navigator's ports), so it composes by name. It holds 400 counts; `init` empties them.

Contract: the window holds this tick's commands, and at most 8 per tick for 400 ticks (the topic's
8 slots). The window's exact meaning (the sum of the last 400 counts) is checked by the
hand-checked case, not by a clause (one tick cannot state it). -/

namespace Px4.Modules.Px4CmdWindow

open Harness Harness.Contract.Lang

def input : Schema :=
  Px4.Modules.Px4Navigator.Ports.input.filter (·.name == "vehicle_command_count")

def output : Schema := #[
  { name := "vehicle_command_last_400_ticks", type := .u32,
    doc := "vehicle_command messages published in the last 400 ticks, this tick included" }]

def contract : Contract where
  assume := [⟨"slots", "vehicle_command_count" ≤. 8⟩]
  guarantee := [
    ⟨"window_holds_tick", "vehicle_command_count" ≤. "vehicle_command_last_400_ticks" ∧.
      "vehicle_command_last_400_ticks" ≤. 3200⟩]

def module : Module where
  name := "px4_cmd_window"
  doc := "OBSERVER: vehicle_command messages in the last 400 ticks (a sliding sum, no PX4 code)"
  params := #[]
  input := input
  output := output
  contract := contract
  exe := "build/modules/px4_cmd_window/px4_cmd_window"
  stack := .px4

end Px4.Modules.Px4CmdWindow
