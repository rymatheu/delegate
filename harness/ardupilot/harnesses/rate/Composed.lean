import Harness.Compose
import ardupilot.modules.rate_pid.Module
import ardupilot.harnesses.rate.Harness

/-! # rate_c: `rate` by composition

The hand-written `rate` (ardupilot/harnesses/rate/Harness.lean) made with the operators of
Harness/Compose.lean from three `rate_pid` instances. -/

namespace Ardupilot.Harnesses.RateC

open Harness

/-- One rate PID as axis `a` (vector component `c`), with the hand-written `rate`'s names. The
attitude controller's calls on the rate PIDs (relax_attitude_controllers, reset_rate_controller_
I_terms, reset_rate_controller_I_terms_smoothly) are made on all three PIDs together
(AC_AttitudeControl.cpp:263-285), so the three axes share one input each, under the attitude
stage's output names `ac_rate_reset_filter`, `ac_rate_reset_i`, `ac_rate_relax_i`. -/
def axis (a c : String) : Except String Node := do
  let n ← inst (.module Ardupilot.Modules.RatePid.module) a
    ["dt", "now_ms", "reset_filter", "reset_i", "relax_i"]
  let n ← rename n [("reset_filter", "ac_rate_reset_filter"), ("reset_i", "ac_rate_reset_i"),
    ("relax_i", "ac_rate_relax_i")]
  let n ← rename n [(s!"{a}_target", s!"target_{c}"), (s!"{a}_measurement", s!"gyro_{c}"),
    (s!"{a}_limit", s!"limit_{a}"), (s!"{a}_pd_scale", s!"pd_scale_{c}"),
    (s!"{a}_i_scale", s!"i_scale_{c}"), (s!"{a}_command", a)]
  hide n [s!"{a}_dmod", s!"{a}_pd_limit"]

/-- The three axes, in the order of rate_controller_run_dt, with `rate`'s regime of the stock
vehicle (stated over the same names). -/
def system (_ : Unit := ()) : Except String Node := do
  let n ← composeAll "rate_c" [← axis "roll" "x", ← axis "pitch" "y", ← axis "yaw" "z"]
  return withRegime n Ardupilot.Harnesses.Rate.stockFlight

end Ardupilot.Harnesses.RateC
