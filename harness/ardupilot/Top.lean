import Harness.Cli
import ardupilot.harnesses.rate.Composed
import ardupilot.modules.mixer.Module

/-! The top-level harness: ArduCopter's inner loop, composed by name and checked when this file
is built. `lake build` makes `.lake/build/bin/top`; `top tree`, `top test`, `top run`,
`top serve`, … (see `Harness.runMain`). -/

open Harness

/-- The mixer with its feed-forward inputs at 0 (the rate PIDs' FF gains are 0). -/
def mixer (_ : Unit := ()) : Except String Node := do
  let m ← fix (.module Ardupilot.Modules.Mixer.module)
    [("roll_ff", .f32 0), ("pitch_ff", .f32 0), ("yaw_ff", .f32 0)]
  rename m [("internal_errors", "mixer_internal_errors")]

/-- The rate controller (three rate PIDs, ardupilot/harnesses/rate/Composed.lean), then the
mixer. -/
def top (_ : Unit := ()) : Except String Node := do
  composeAll "top" [← Ardupilot.Harnesses.RateC.system, ← mixer]

#harness_check top

def main (args : List String) : IO UInt32 := runMain top args
