import Harness.Compose
import ardupilot.harnesses.rate.Composed
import ardupilot.modules.mixer.Module

/-! # inner_loop_c: `inner_loop` by composition

`rate_c` then the mixer with its feed-forward inputs at 0. The names do the wiring: rate_c's
`roll`, `pitch`, `yaw` feed the mixer's (same tick), the mixer's `limit_roll/pitch/yaw` feed
rate_c's (previous tick, false at the first), `dt` is one input of both. -/

namespace Ardupilot.Harnesses.InnerLoopC

open Harness

/-- The composite. -/
def system (_ : Unit := ()) : Except String Node := do
  let mixer ← fix (.module Ardupilot.Modules.Mixer.module)
    [("roll_ff", .f32 0), ("pitch_ff", .f32 0), ("yaw_ff", .f32 0)]
  compose "inner_loop_c" (← Ardupilot.Harnesses.RateC.system)
    (← rename mixer [("internal_errors", "mixer_internal_errors")])

end Ardupilot.Harnesses.InnerLoopC
