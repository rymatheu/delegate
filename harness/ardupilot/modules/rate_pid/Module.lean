import Harness.Module

/-! # rate_pid: one ArduPilot rate PID

One `AC_PID` (libraries/AC_PID), stepped by `AC_PID::update_all` as ArduCopter's rate controller
calls it (AC_AttitudeControl_Multi::rate_controller_run). The executable is built by
`ardupilot/build.sh rate_pid` from the real AC_PID.cpp and the ArduPilot code on its step path;
see adapter.cpp for the cut and stubs.cpp for what is outside. -/

namespace Ardupilot.Modules.RatePid

open Harness Harness.Contract.Lang

def params : Schema := #[
  { name := "kp", type := .f32, doc := "P gain (_kp)" },
  { name := "ki", type := .f32, doc := "I gain (_ki)" },
  { name := "kd", type := .f32, doc := "D gain (_kd)" },
  { name := "kimax", type := .f32, doc := "integrator limit (_kimax)" },
  { name := "kpdmax", type := .f32, doc := "P+D sum limit, 0 disables (_kpdmax)" },
  { name := "filt_T_hz", type := .f32, doc := "target filter cutoff, Hz (_filt_T_hz)" },
  { name := "filt_E_hz", type := .f32, doc := "error filter cutoff, Hz (_filt_E_hz)" },
  { name := "filt_D_hz", type := .f32, doc := "derivative filter cutoff, Hz (_filt_D_hz)" },
  { name := "slew_max", type := .f32, doc := "slew rate limit, 0 disables (_slew_rate_max)" }]

def input : Schema := #[
  { name := "target", type := .f32, doc := "rate target" },
  { name := "measurement", type := .f32, doc := "measured rate" },
  { name := "dt", type := .f32, doc := "time step, s" },
  { name := "limit", type := .bool, doc := "motors saturated: integrator may shrink, not grow" },
  { name := "pd_scale", type := .f32, doc := "P and D scale (_pd_scale)" },
  { name := "i_scale", type := .f32, doc := "I scale (_i_scale)" },
  { name := "now_ms", type := .u32, doc := "the clock AP_HAL::millis() reads (slew limiter)" },
  { name := "reset_filter", type := .bool,
    doc := "AC_PID::reset_filter() was called after the previous update_all (by the attitude \
      controller's relax_attitude_controllers, AC_AttitudeControl.cpp:263-265); applied before \
      this step's update_all" },
  { name := "reset_i", type := .bool,
    doc := "AC_PID::reset_I() was called after the previous update_all \
      (reset_rate_controller_I_terms, AC_AttitudeControl.cpp:275-277); applied before this \
      step's update_all, after reset_filter" },
  { name := "relax_i", type := .bool,
    doc := "AC_PID::relax_integrator(0, dt, AC_ATTITUDE_RATE_RELAX_TC = 0.16) was called after \
      the previous update_all (reset_rate_controller_I_terms_smoothly, \
      AC_AttitudeControl.cpp:283-285); applied before this step's update_all, after reset_i, \
      with this step's dt" }]

def output : Schema := #[
  { name := "command", type := .f32, doc := "update_all's result: P + D + I" },
  { name := "integrator", type := .f32, doc := "get_i()" },
  { name := "p_term", type := .f32, doc := "get_p()" },
  { name := "d_term", type := .f32, doc := "get_d()" },
  { name := "dmod", type := .f32, doc := "slew limiter's gain modifier" },
  { name := "pd_limit", type := .bool, doc := "the P+D sum limit acted" },
  { name := "internal_errors", type := .u32, doc := "ArduPilot internal errors raised since init" }]

/-- The contract as first stated (docs/5-creating-a-harness.md), with the parameter
assumptions it left open. Its campaign refuted command_finite and no_internal_error
(docs/8-first-example.md); kept for the record, not used. -/
def contractAsFirstStated : Contract where
  assume := [
    ⟨"gains_finite", finite "kp" ∧. finite "ki" ∧. finite "kd"⟩,
    ⟨"kimax_range", 0 ≤. "kimax" ∧. finite "kimax"⟩,
    ⟨"kpdmax_range", 0 ≤. "kpdmax" ∧. finite "kpdmax"⟩,
    ⟨"filters_range", 0 ≤. "filt_T_hz" ∧. finite "filt_T_hz" ∧. 0 ≤. "filt_E_hz" ∧.
        finite "filt_E_hz" ∧. 0 ≤. "filt_D_hz" ∧. finite "filt_D_hz"⟩,
    ⟨"slew_range", 0 ≤. "slew_max" ∧. finite "slew_max"⟩,
    ⟨"signals_finite", finite "target" ∧. finite "measurement"⟩,
    ⟨"dt_range", 0 <. "dt" ∧. "dt" ≤. 0.01⟩,
    ⟨"scales_range", 0 ≤. "pd_scale" ∧. "pd_scale" ≤. 1 ∧. 0 ≤. "i_scale" ∧. "i_scale" ≤. 1⟩]
  guarantee := [
    ⟨"integrator_bounded", abs "integrator" ≤. "kimax"⟩,
    ⟨"command_finite", finite "command"⟩,
    ⟨"no_internal_error", "internal_errors" =. 0⟩]

/-- The second statement. Against the first statement, the signals and the three gains are
bounded: finiteness alone lets `target - measurement`, `error * kp`, `derivative * kd` and the
integrator increment overflow to ∞, after which the error filter makes NaN
(docs/8-first-example.md). Not refuted; replaced by `contract` (wider pd_scale, one more
guarantee clause). Kept for the record, not used. -/
def contractSecond : Contract where
  assume := [
    ⟨"gains_bounded", abs "kp" ≤. 1e4 ∧. abs "ki" ≤. 1e4 ∧. abs "kd" ≤. 1e4⟩,
    ⟨"kimax_range", 0 ≤. "kimax" ∧. finite "kimax"⟩,
    ⟨"kpdmax_range", 0 ≤. "kpdmax" ∧. finite "kpdmax"⟩,
    ⟨"filters_range", 0 ≤. "filt_T_hz" ∧. finite "filt_T_hz" ∧. 0 ≤. "filt_E_hz" ∧.
        finite "filt_E_hz" ∧. 0 ≤. "filt_D_hz" ∧. finite "filt_D_hz"⟩,
    ⟨"slew_range", 0 ≤. "slew_max" ∧. finite "slew_max"⟩,
    ⟨"signals_bounded", abs "target" ≤. 1e4 ∧. abs "measurement" ≤. 1e4⟩,
    ⟨"dt_range", 0 <. "dt" ∧. "dt" ≤. 0.01⟩,
    ⟨"scales_range", 0 ≤. "pd_scale" ∧. "pd_scale" ≤. 1 ∧. 0 ≤. "i_scale" ∧. "i_scale" ≤. 1⟩]
  guarantee := [
    ⟨"integrator_bounded", abs "integrator" ≤. "kimax"⟩,
    ⟨"command_finite", finite "command"⟩,
    ⟨"no_internal_error", "internal_errors" =. 0⟩]

/-- The contract. Against the second statement:
* `scales_range` admits pd_scale up to 2 (it was 1). The attitude stage hands the rate PIDs
  `_pd_scale`, which update_throttle_gain_boost multiplies by constrain(ATC_THR_G_BOOST + 1, 1,
  2) on a fast throttle change (AC_AttitudeControl_Multi.cpp:420-421), so with ATC_THR_G_BOOST > 0
  it exceeds 1. update_all multiplies P and D by it after the slew modifier and before the P+D
  limit (AC_PID.cpp:280-282); nothing else reads it.
* `command_magnitude` added: |command| ≤ 7e15 + kimax, the hand-written `rate` system's
  code-derived bound (ardupilot/harnesses/rate/Harness.lean, guaranteeFromCode) with pd_scale ≤ 2: |P| ≤
  2e4 · 1e4 · 2, |D| ≤ (4e4 / FLT_EPSILON) · 1e4 · 2 = 6.7e15 (the derivative is computed only
  when dt ≥ FLT_EPSILON, AC_PID.cpp:256), the slew modifier at most 1, the P+D limit only scales
  down, |I| ≤ kimax. Stated here so that a composition carries it to the mixer's
  `commands_bounded` (docs/9-nesting.md, "Open obligation").
The inputs `reset_filter`, `reset_i`, `relax_i` (the attitude stage's calls on the rate PIDs) need
no assumption: each is a Boolean, and relax_integrator reads dt, which `dt_range` bounds. -/
def contract : Contract where
  assume := contractSecond.assume.map fun c => if c.name != "scales_range" then c else
    ⟨"scales_range", 0 ≤. "pd_scale" ∧. "pd_scale" ≤. 2 ∧. 0 ≤. "i_scale" ∧. "i_scale" ≤. 1⟩
  guarantee := contractSecond.guarantee ++
    [⟨"command_magnitude", abs "command" ≤. 7e15 + .var "kimax"⟩]

/-- What a campaign counts: the resets applied, and P and D scaled above 1. -/
def coverage : List Clause := [
  ⟨"reset_i", "reset_i"⟩,
  ⟨"relax_i", "relax_i" ∧. ¬. "reset_i"⟩,
  ⟨"reset_filter", "reset_filter"⟩,
  ⟨"pd_scale_above_1", 1 <. "pd_scale"⟩]

def module : Module where
  name := "rate_pid"
  doc := "one ArduPilot AC_PID stepped by update_all"
  params := params
  input := input
  output := output
  contract := contract
  exe := "build/modules/rate_pid/rate_pid"
  stack := .ardupilot
  coverage := coverage

end Ardupilot.Modules.RatePid
