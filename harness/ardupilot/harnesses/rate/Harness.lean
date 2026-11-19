import Harness.System
import ardupilot.modules.rate_pid.Module

/-! # rate: the three rate PIDs of ArduCopter's rate controller

`AC_AttitudeControl_Multi::rate_controller_run_dt` (libraries/AC_AttitudeControl/
AC_AttitudeControl_Multi.cpp) calls `update_all` on the roll, pitch and yaw rate PIDs:

    _motors.set_roll(get_rate_roll_pid().update_all(ang_vel_body.x, gyro_rads.x, dt,
        _motors.limit.roll, _pd_scale.x, _i_scale.x) + _actuator_sysid.x);

and likewise for pitch (y) and yaw (z). Between the PIDs it only routes values, so here it is
wires: three instances of the module `rate_pid`, each fed from the system's inputs and its own
prefixed parameters. Left outside this system, because they compute rather than route: the
`_sysid_ang_vel_body_rads` added to the target (the inputs `target_*` are the targets after that
addition), the `_actuator_sysid` added to each command (the outputs are the PIDs' results before
it), the feed-forward (`get_ff`, not part of `update_all`'s result), and the throttle gain boost
and mix updates. The clock `now_ms` is one input shared by the three PIDs (ArduPilot reads
`AP_HAL::millis()` once per PID; the three reads can differ when a millisecond boundary falls
between them). -/

namespace Ardupilot.Harnesses.Rate

open Harness Harness.Contract.Lang

/-- The axes: instance name and the vector component it reads. -/
def axes : List (String × String) := [("roll", "x"), ("pitch", "y"), ("yaw", "z")]

private def v (n : String) : Expr := .var n

/-- The nine `rate_pid` parameters per axis, prefixed: `roll_kp`, …, `yaw_slew_max`. -/
def params : Schema :=
  axes.toArray.flatMap fun (a, _) => Ardupilot.Modules.RatePid.params.prefixed s!"{a}_"

private def f32 (name doc : String) : Field := { name, type := .f32, doc }

def input : Schema :=
  (axes.toArray.map fun (a, c) =>
    f32 s!"target_{c}" s!"{a} rate target, rad/s (ang_vel_body.{c})") ++
  (axes.toArray.map fun (a, c) => f32 s!"gyro_{c}" s!"measured {a} rate, rad/s (gyro_rads.{c})") ++
  #[f32 "dt" "time step, s"] ++
  (axes.toArray.map fun (a, _) =>
    ({ name := s!"limit_{a}", type := .bool, doc := s!"_motors.limit.{a}" } : Field)) ++
  (axes.toArray.map fun (_, c) => f32 s!"pd_scale_{c}" s!"_pd_scale.{c}") ++
  (axes.toArray.map fun (_, c) => f32 s!"i_scale_{c}" s!"_i_scale.{c}") ++
  #[{ name := "now_ms", type := .u32, doc := "the clock AP_HAL::millis() reads, for all three" }]

def output : Schema :=
  (axes.toArray.map fun (a, _) => f32 a s!"{a} command: update_all's result (_motors.set_{a})") ++
  (axes.toArray.map fun (a, _) => f32 s!"{a}_integrator" s!"{a} PID integrator") ++
  (axes.toArray.map fun (a, _) =>
    ({ name := s!"{a}_internal_errors", type := .u32,
       doc := s!"{a} PID: internal errors since init" } : Field)) ++
  (axes.toArray.map fun (a, _) => f32 s!"{a}_p_term" s!"{a} PID: P after slew, scale and limit") ++
  (axes.toArray.map fun (a, _) => f32 s!"{a}_d_term" s!"{a} PID: D after slew, scale and limit")

/-- One `rate_pid` instance for axis `a` reading vector component `c`. The attitude
controller's calls on the PIDs (`reset_filter`, `reset_i`, `relax_i`, added to `rate_pid` with the
attitude stage) are not inputs of this hand-written system: they are fed `false`, so it stays
the rate controller of docs/9-nesting.md. The composed `rate_c` (Composed.lean) carries them. -/
def child (a c : String) : Child where
  name := a
  node := .module Ardupilot.Modules.RatePid.module
  params := Wire.paramsPrefixed s!"{a}_" Ardupilot.Modules.RatePid.params
  input := Wire.inputs [("target", s!"target_{c}"), ("measurement", s!"gyro_{c}"), ("dt", "dt"),
    ("limit", s!"limit_{a}"), ("pd_scale", s!"pd_scale_{c}"), ("i_scale", s!"i_scale_{c}"),
    ("now_ms", "now_ms")] ++
    ["reset_filter", "reset_i", "relax_i"].map fun f => ⟨f, .const ⟨.bool, 0⟩⟩

/-- The parameter assumptions of one axis: `rate_pid`'s, on that axis's parameters. -/
def axisParamAssume (a : String) : List Clause :=
  let p (n : String) := v s!"{a}_{n}"
  [⟨s!"{a}_gains_bounded", abs (p "kp") ≤. 1e4 ∧. abs (p "ki") ≤. 1e4 ∧. abs (p "kd") ≤. 1e4⟩,
   ⟨s!"{a}_kimax_range", 0 ≤. p "kimax" ∧. finite (p "kimax")⟩,
   ⟨s!"{a}_kpdmax_range", 0 ≤. p "kpdmax" ∧. finite (p "kpdmax")⟩,
   ⟨s!"{a}_filters_range", 0 ≤. p "filt_T_hz" ∧. finite (p "filt_T_hz") ∧. 0 ≤. p "filt_E_hz" ∧.
      finite (p "filt_E_hz") ∧. 0 ≤. p "filt_D_hz" ∧. finite (p "filt_D_hz")⟩,
   ⟨s!"{a}_slew_range", 0 ≤. p "slew_max" ∧. finite (p "slew_max")⟩]

/-- The assumption: each axis bounded as `rate_pid`'s assumption bounds it (so each child's
assumption follows from it). -/
def assume : List Clause :=
  axes.flatMap (fun (a, _) => axisParamAssume a) ++ [
    ⟨"signals_bounded", abs (v "target_x") ≤. 1e4 ∧. abs (v "target_y") ≤. 1e4 ∧.
      abs (v "target_z") ≤. 1e4 ∧. abs (v "gyro_x") ≤. 1e4 ∧. abs (v "gyro_y") ≤. 1e4 ∧.
      abs (v "gyro_z") ≤. 1e4⟩,
    ⟨"dt_range", 0 <. v "dt" ∧. v "dt" ≤. 0.01⟩] ++
    axes.map fun (_, c) =>
      ⟨s!"scales_range_{c}", 0 ≤. v s!"pd_scale_{c}" ∧. v s!"pd_scale_{c}" ≤. 1 ∧.
        0 ≤. v s!"i_scale_{c}" ∧. v s!"i_scale_{c}" ≤. 1⟩

/-- Each child's guarantee, on the outputs that carry it. -/
def guaranteeChildren : List Clause :=
  axes.flatMap fun (a, _) => [
    ⟨s!"{a}_integrator_bounded", abs (v s!"{a}_integrator") ≤. v s!"{a}_kimax"⟩,
    ⟨s!"{a}_command_finite", finite (v a)⟩,
    ⟨s!"{a}_no_internal_error", v s!"{a}_internal_errors" =. 0⟩]

/-- A bound on the command through the P+D limit, as stated in the second round:
`kpdmax < FLT_EPSILON ∨ |cmd| ≤ (kpdmax + kimax) * 1.000001`. Refuted (inner_loop, regime
flight, seed 11, 200 x 100: case 135 step 24, margin -1.490116e-8; the case, an inner_loop
case, is copied to ardupilot/harnesses/rate/command-bound-case.json). When the limit acts,
AC_PID::update_all scales P and D separately, `P_out *= kpdmax / |P+D|`, `D_out *= ...`
(AC_PID.cpp:287-292), and returns `P_out + D_out + I_out` (:310). With P and D of
opposite signs and larger than their sum, the re-added sum carries the rounding of the large
terms, an error of about one ulp of |P_out| + |D_out|, not of kpdmax: in the counterexample
P_out = -3.9527, D_out = 4.1806, kpdmax = 0.22783756 and P_out + D_out = 0.22783780. With
large gains the excess grows with |P_out| + |D_out|. Kept for the record, not used. -/
def commandBoundedAsFirstStated (a : String) : Clause :=
  ⟨s!"{a}_command_bounded", v s!"{a}_kpdmax" <. 1.1920929e-7 ∨.
    abs (v a) ≤. (v s!"{a}_kpdmax" + v s!"{a}_kimax") * 1.000001⟩

/-- Bounds that follow from the code of update_all, on the exposed P and D terms:
* `command_sum`: the command is exactly `P_out + D_out + I_out` in binary32, in that order
  (AC_PID.cpp:310), and get_p, get_d, get_i return those three values.
* `pd_limited`: with the P+D limit on (kpdmax ≥ FLT_EPSILON, `is_positive`), |P_out + D_out| ≤
  kpdmax up to rounding. Scaling by s = kpdmax/|P+D| (one rounding in s, one in |P+D|) gives
  |s (P+D)| ≤ kpdmax (1 + 2u); each scaled term adds at most u |term| and the sum u more, so
  |P_out + D_out| ≤ kpdmax (1 + 3u) + u (|P_out| + |D_out|) (u = 2^-24, first order). The clause
  allows 8u on kpdmax and 3u on the terms, which also covers the binary32 rounding of its own
  right-hand side (three operations).
* `command_magnitude`: |command| ≤ 3.5e15 + kimax. Under the assumption |P| ≤ |error| |kp| ≤
  2e4 * 1e4 (the target and error filters are convex combinations of bounded values), and the
  derivative is computed only when dt ≥ FLT_EPSILON (AC_PID.cpp:256), so
  |D| ≤ (4e4 / 1.19e-7) * 1e4 = 3.36e15; the slew modifier and pd_scale are at most 1 and the
  P+D limit only scales down; |I| ≤ kimax. 3.5e15 leaves room for rounding. -/
def guaranteeFromCode : List Clause :=
  axes.flatMap fun (a, _) =>
    let p := v s!"{a}_p_term"
    let d := v s!"{a}_d_term"
    [⟨s!"{a}_command_sum", v a =. p + d + v s!"{a}_integrator"⟩,
     ⟨s!"{a}_pd_limited", v s!"{a}_kpdmax" <. 1.1920929e-7 ∨.
        abs (p + d) ≤. v s!"{a}_kpdmax" * 1.0000005 + (abs p + abs d) * 1.8e-7⟩,
     ⟨s!"{a}_command_magnitude", abs (v a) ≤. 3.5e15 + v s!"{a}_kimax"⟩]

/-- The contract. -/
def contract : Contract where
  assume := assume
  guarantee := guaranteeChildren ++ guaranteeFromCode

/-! ### The stock vehicle (regime `stock_flight`) -/

/-- ArduCopter's default rate-PID parameters (libraries/AC_AttitudeControl, read only):
roll and pitch P 0.135, I 0.135, D 0.0036, IMAX 0.5 (AC_AttitudeControl_Multi.h:11, 14, 17,
20); yaw P 0.180, I 0.018, D 0, IMAX 0.5 (:26, 29, 32, 35); target and derivative filters
RPY_FILT_HZ = 20 on all axes (:23, used at :113, 115, 128, 130, 143, 145); error filter 0 on
roll and pitch (:114, 129) and YAW_FILT_HZ = 2.5 on yaw (:38, used at :144); slew limit 0
(`.srmax = 0`, :116, 131, 146); PDMX 0 (AC_PID.cpp:73). -/
def stockParams : List Clause :=
  let gains (a : String) (kp ki kd fe : Expr) : Clause :=
    ⟨s!"{a}_stock", v s!"{a}_kp" =. kp ∧. v s!"{a}_ki" =. ki ∧. v s!"{a}_kd" =. kd ∧.
      v s!"{a}_kimax" =. 0.5 ∧. v s!"{a}_kpdmax" =. 0 ∧. v s!"{a}_filt_T_hz" =. 20 ∧.
      v s!"{a}_filt_E_hz" =. fe ∧. v s!"{a}_filt_D_hz" =. 20 ∧. v s!"{a}_slew_max" =. 0⟩
  [gains "roll" 0.135 0.135 0.0036 0, gains "pitch" 0.135 0.135 0.0036 0,
   gains "yaw" 0.180 0.018 0 2.5]

/-- Flight-like signals: rate targets and gyro within 3 rad/s, the loop time near 1/400 s, and
the PD and I scales at 1 (reset to VECTORF_111 every loop, AC_AttitudeControl.cpp:293-294). -/
def stockSignals : List Clause := [
  ⟨"stock_rates", abs (v "target_x") ≤. 3 ∧. abs (v "target_y") ≤. 3 ∧. abs (v "target_z") ≤. 3 ∧.
    abs (v "gyro_x") ≤. 3 ∧. abs (v "gyro_y") ≤. 3 ∧. abs (v "gyro_z") ≤. 3⟩,
  ⟨"stock_dt", 0.0024 ≤. v "dt" ∧. v "dt" ≤. 0.0026⟩,
  ⟨"stock_scales", v "pd_scale_x" =. 1 ∧. v "pd_scale_y" =. 1 ∧. v "pd_scale_z" =. 1 ∧.
    v "i_scale_x" =. 1 ∧. v "i_scale_y" =. 1 ∧. v "i_scale_z" =. 1⟩]

/-- The stock vehicle's rate controller in flight. -/
def stockFlight : Regime where
  name := "stock_flight"
  doc := "ArduCopter's default rate gains, flight-like rates, 400 Hz"
  clauses := stockParams ++ stockSignals
  hints := [.increasing "now_ms" 1000 2 3]

/-- The system `rate`. -/
def system : Sys where
  name := "rate"
  doc := "the three rate PIDs of AC_AttitudeControl_Multi::rate_controller_run_dt"
  params := params
  input := input
  output := output
  children := axes.map fun (a, c) => child a c
  outputs := axes.flatMap fun (a, _) =>
    Wire.outsOf a [(a, "command"), (s!"{a}_integrator", "integrator"),
      (s!"{a}_internal_errors", "internal_errors"), (s!"{a}_p_term", "p_term"),
      (s!"{a}_d_term", "d_term")]
  contract := contract
  regimes := [stockFlight]

end Ardupilot.Harnesses.Rate
