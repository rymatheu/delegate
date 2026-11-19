import Harness.Compose
import ardupilot.harnesses.chain.Discharges
import ardupilot.harnesses.rate.Composed
import ardupilot.modules.mixer.Module
import ardupilot.modules.guidance.Module
import ardupilot.modules.position.Module
import ardupilot.modules.attitude.Module

/-! # ap_ctl: ArduCopter's controller chain

`rate_c`, `mixer`, `guidance`, `position`, `attitude`, in the brief's tick order, composed by
port name with no rename. Same tick: the mixer reads the rate commands; the position stage reads
the guidance stage's targets and hand-over calls and the mixer's limit flags; the attitude stage
reads the position stage's thrust vector and collective call and the mixer's throttle state.
Previous tick (`prev`, as in ArduCopter's loop): the rate PIDs read the attitude stage's rate
targets, PID scales and resets and the mixer's limit flags; the guidance stage reads the
position stage's state and limits; the position stage reads the attitude stage's targets.

Inputs of the composite: the estimator's signals (`gyro_*`, `est_*`), the supervisor's arming,
spool and commands (`armed`, …, `cmd_*`), time, battery and air density, and `throttle_hover`.
`throttle_hover` has no producer: ArduCopter learns it in Copter::update_throttle_hover
(Attitude.cpp:32, MOT_HOVER_LEARN) and hands it to the motors; here it is an input that the
regimes fix to the mixer's parameter `thst_hover` (the value a vehicle with MOT_HOVER_LEARN = 0
uses). Position inputs fixed: `tgt_ne_only = false` (AC_Loiter, which hands NE-only targets,
is its own stage, `loiter`, with its own ports `lt_…`) and `tgt_terrain_d = 0` (AC_WPNav's
set_pos_terrain_target_D_m(0), terrain out of scope in the guidance stage); the loiter stage's
ports `lt_…` off (no loiter stage in this chain). -/

namespace Ardupilot.Harnesses.ApCtl

open Harness Harness.Contract.Lang

/-- The position stage with the inputs nothing produces fixed, and the values its outputs have
before its first step, which the guidance stage reads at the first tick (`prev`): the limits
AC_PosControl's constructor sets (POSCONTROL_SPEED_MS 5, POSCONTROL_SPEED_UP_MS 2.5,
POSCONTROL_SPEED_DOWN_MS 1.5, POSCONTROL_ACCEL_NE_MSS 1, POSCONTROL_ACCEL_D_MSS 2.5;
AC_PosControl.h:19-29, AC_PosControl.cpp:362-366). With the default 0 the first tick failed the
guidance stage's `pc_limits_range` in every case (ap_ctl, auto_wp seed 1: 30 of 30 cases at
step 0). -/
def positionOpen (_ : Unit := ()) : Except String Node := do
  let n ← fix (.module Ardupilot.Modules.Position.module)
    [("tgt_ne_only", .bool false), ("tgt_terrain_d", .f32 0)]
  withInit n [("pc_ne_max_speed", .f32 5), ("pc_max_speed_up", .f32 2.5),
    ("pc_max_speed_down", .f32 1.5), ("pc_ne_max_accel", .f32 1), ("pc_d_max_accel", .f32 2.5)]

/-- `positionOpen` with the loiter stage's ports off (`Position.loiterOffFix`): the chains
without a loiter stage. -/
def position (_ : Unit := ()) : Except String Node := do
  fix (← positionOpen) Ardupilot.Modules.Position.loiterOffFix

/-- The attitude stage with the values its outputs have before its first step, which the rate
PIDs and the position stage read at the first tick: _pd_scale and _i_scale (1, 1, 1),
AC_AttitudeControl.h:689, 695; get_althold_lean_angle_max_rad() of a fresh controller, the
10 degree floor AC_ATTITUDE_CONTROL_ANGLE_LIMIT_MIN; and the two values that depend on a
parameter, taken at ArduCopter's defaults: lean_angle_max_rad() = radians(ATC_ANGLE_MAX = 30)
and get_bf_feedforward() = ATC_RATE_FF_ENAB = 1. A `withInit` value is a constant, so for other
ATC_ANGLE_MAX or ATC_RATE_FF_ENAB the first tick sees the default's value (the X500's
parameters keep both defaults). With the default 0 the first tick failed the position stage's
`ac_lean_range` in every case (auto_wp seed 1: 30 of 30 cases at step 0). -/
def attitude (_ : Unit := ()) : Except String Node :=
  withInit (.module Ardupilot.Modules.Attitude.module) [("pd_scale_x", .f32 1), ("pd_scale_y", .f32 1),
    ("pd_scale_z", .f32 1), ("i_scale_x", .f32 1), ("i_scale_y", .f32 1), ("i_scale_z", .f32 1),
    ("ac_althold_lean_angle_max", .f32 0.17453292), ("ac_lean_angle_max", .f32 0.5235988),
    ("ac_bf_feedforward", .bool true)]

/-- The composition, without regimes. -/
def chain (_ : Unit := ()) : Except String Node := do
  composeAll "ap_ctl" [← Ardupilot.Harnesses.RateC.system, .module Ardupilot.Modules.Mixer.module,
    .module Ardupilot.Modules.Guidance.module, ← position, ← attitude]

private def v (n : String) : Expr := .var n

/-- `e₁ ∧ … ∧ eₙ`. -/
def allOf : List Expr → Expr
  | [] => tt
  | [e] => e
  | e :: es => e ∧. allOf es

/-- The clauses that mention only the given fields (the composite's own). -/
def own (fields : List String) (cs : List Clause) : List Clause :=
  cs.filter fun c => c.expr.vars.all fields.contains

/-- Every command Boolean of a stage (`cmd_<stage>_<method>`), from its input schema. -/
def cmdBools (s : Schema) (pre : String) : List String :=
  (s.toList.filter fun f => f.type == .bool && f.name.startsWith pre &&
    f.doc.endsWith "is called this tick" || (f.type == .bool && f.name.startsWith pre &&
    (f.doc.startsWith "AC_WPNav::" || f.doc.startsWith "AC_WPNav ") )).map (·.name)

/-- The command Booleans that are off, except `keep`. -/
def othersOff (all keep : List String) : Expr :=
  allOf ((all.filter (!keep.contains ·)).map fun c => ¬. v c)

/-- The stock parameters of every stage, ArduCopter's defaults (each stage's `stockParams`),
and the flight-like signals of the estimator, the clock and the battery. -/
def stockAndSignals : List Clause :=
  Ardupilot.Modules.Mixer.stockParams ++ Ardupilot.Harnesses.Rate.stockParams ++ Ardupilot.Modules.Position.stockParams ++
  Ardupilot.Modules.Attitude.stockParams ++ Ardupilot.Modules.Guidance.stockParams ++ [
  -- the hover throttle input fixed to the mixer's stock MOT_THST_HOVER (0.35, stockParams);
  -- written as a literal so that the generator can draw it
  ⟨"hover_is_parameter", v "throttle_hover" =. 0.35⟩,
  ⟨"loop_400hz", 0.0024 ≤. v "dt" ∧. v "dt" ≤. 0.0026⟩,
  ⟨"est_valid", v "est_pos_ok" ∧. v "est_vel_ok" ∧.
      v "est_pos_rate_d_ok"⟩,
  ⟨"est_near_hover", abs (v "est_vel_n") ≤. 2 ∧. abs (v "est_vel_e") ≤. 2 ∧.
      abs (v "est_vel_d") ≤. 2 ∧. abs (v "est_pos_rate_d") ≤. 2 ∧.
      -11 ≤. v "est_accel_ef_z" ∧. v "est_accel_ef_z" ≤. -8.5 ∧. abs (v "est_pos_n") ≤. 20 ∧.
      abs (v "est_pos_e") ≤. 20 ∧. abs (v "est_pos_d") ≤. 20 ∧.
      v "est_gain_scaler_xy" =. 1 ∧. v "est_gain_scaler_z" =. 1 ∧.
      v "est_pos_ne_reset_count" =. 0 ∧. v "est_pos_d_reset_count" =. 0⟩,
  ⟨"est_attitude", abs (v "est_roll") ≤. 0.5 ∧. abs (v "est_pitch") ≤. 0.5 ∧.
      abs (v "gyro_x") ≤. 2 ∧. abs (v "gyro_y") ≤. 2 ∧. abs (v "gyro_z") ≤. 2⟩,
  ⟨"stock_battery_readings", 22 ≤. v "batt_voltage" ∧. v "batt_voltage" ≤. 25.2 ∧.
      22 ≤. v "batt_resting_voltage" ∧. v "batt_resting_voltage" ≤. 25.2 ∧. 5 ≤. v "batt_current" ∧.
      v "batt_current" ≤. 40 ∧. v "batt_current_ok" ∧. 0.01 ≤. v "batt_resistance" ∧.
      v "batt_resistance" ≤. 0.05⟩,
  ⟨"stock_air", 0.9 ≤. v "air_density_ratio" ∧. v "air_density_ratio" ≤. 1.1⟩,
  ⟨"no_ff", v "roll_ff" =. 0 ∧. v "pitch_ff" =. 0 ∧. v "yaw_ff" =. 0⟩]

def atBoot : Expr := v "now_ms" ≤. 1000

/-- Every call-order field 0: the stages run their fixed orders, which are the orders of the
mode code these regimes stand for. -/
def fixedOrder (fields : List String) : Clause :=
  ⟨"fixed_order", allOf ((fields.filter fun f => f.startsWith "cmd_" && f.endsWith "_seq").map
    fun f => v f =. 0)⟩

/-- AUTO with a straight waypoint leg (ModeAuto::wp_start and wp_run, mode_auto.cpp:465-505,
1134-1152), armed and flying: at the first tick AC_WPNav::wp_and_spline_init_m (which
initializes the position controller at its stopping point) and set_wp_destination_NED_m; every
tick update_estimates (Copter::read_inertia), update_wpnav (which hands the targets and runs the
NE update), D_update_controller, then input_thrust_vector_heading, one attitude input per tick;
the motors spooled to THROTTLE_UNLIMITED. The commands are consistent: the controllers are
initialized at the first tick before any update. The estimator's signals are random near hover
(they are not a trajectory). -/
def autoWp (fields : List String) : Regime :=
  let pos := cmdBools Ardupilot.Modules.Position.input "cmd_position_"
  let att := cmdBools Ardupilot.Modules.Attitude.input "cmd_attitude_"
  let gd := cmdBools Ardupilot.Modules.Guidance.input "cmd_guidance_"
  { name := "auto_wp"
    doc := "stock parameters, AUTO waypoint leg: wpnav init and destination at the first tick, \
      then update_wpnav, D_update_controller, input_thrust_vector_heading every tick"
    clauses := own fields (stockAndSignals ++ [fixedOrder fields,
      ⟨"armed_flying", v "armed" ∧. v "interlock" ∧. v "spool_desired" =. 2 ∧.
          v "clear_spoolup_block"⟩,
      ⟨"position_cmds", v "cmd_position_update_estimates" ∧.
          ¬. v "cmd_position_update_estimates_high_vibes" ∧. v "cmd_position_D_update_controller" ∧.
          othersOff pos ["cmd_position_update_estimates", "cmd_position_D_update_controller",
            "cmd_position_set_reset_handling_method"]⟩,
      ⟨"guidance_cmds", v "cmd_guidance_update_wpnav" ∧.
          ((atBoot ∧. v "cmd_guidance_wp_and_spline_init_m" ∧.
            v "cmd_guidance_set_wp_destination_NED_m") ∨.
           (¬. atBoot ∧. ¬. v "cmd_guidance_wp_and_spline_init_m" ∧.
            ¬. v "cmd_guidance_set_wp_destination_NED_m")) ∧.
          othersOff gd ["cmd_guidance_update_wpnav", "cmd_guidance_wp_and_spline_init_m",
            "cmd_guidance_set_wp_destination_NED_m"]⟩,
      ⟨"guidance_args", v "cmd_guidance_wp_and_spline_init_m_speed_ms" =. 0 ∧.
          v "cmd_guidance_wp_and_spline_init_m_stopping_point_n" =. 0 ∧.
          v "cmd_guidance_wp_and_spline_init_m_stopping_point_e" =. 0 ∧.
          v "cmd_guidance_wp_and_spline_init_m_stopping_point_d" =. 0 ∧.
          abs (v "cmd_guidance_set_wp_destination_NED_m_destination_n") ≤. 20 ∧.
          abs (v "cmd_guidance_set_wp_destination_NED_m_destination_e") ≤. 20 ∧.
          abs (v "cmd_guidance_set_wp_destination_NED_m_destination_d") ≤. 20 ∧.
          v "cmd_guidance_set_wp_destination_NED_m_arc_rad" =. 0⟩,
      ⟨"attitude_cmds", v "cmd_attitude_input_thrust_vector_heading" ∧.
          v "cmd_attitude_input_thrust_vector_heading_heading_mode" =. 1 ∧.
          abs (v "cmd_attitude_input_thrust_vector_heading_yaw_angle") ≤. 3.1415927 ∧.
          abs (v "cmd_attitude_input_thrust_vector_heading_yaw_rate") ≤. 1 ∧.
          ¬. v "cmd_attitude_pos_throttle_after_input" ∧.
          othersOff att ["cmd_attitude_input_thrust_vector_heading",
            "cmd_attitude_landed_gain_reduction", "cmd_attitude_set_throttle_mix_max"] ∧.
          ¬. v "cmd_attitude_landed_gain_reduction_landed"⟩])
    hints := [.increasing "now_ms" 1000 2 3, .increasing "now_us" 1000000 2400 2600] }

/-- Armed on the ground in GUIDED before takeoff (Mode::make_safe_ground_handling every tick,
mode.cpp:658-690): ground idle, the controllers relaxed, the attitude level. GUIDED's
initialization at mode entry (pva_control_start, mode_guided.cpp:360-380) is not issued (see the
clause `position_no_init`). -/
def groundIdle (fields : List String) : Regime :=
  let pos := cmdBools Ardupilot.Modules.Position.input "cmd_position_"
  let att := cmdBools Ardupilot.Modules.Attitude.input "cmd_attitude_"
  let gd := cmdBools Ardupilot.Modules.Guidance.input "cmd_guidance_"
  let initCmds := ["cmd_position_NE_set_max_speed_accel_m",
    "cmd_position_NE_set_correction_speed_accel_m", "cmd_position_D_set_max_speed_accel_m",
    "cmd_position_D_set_correction_speed_accel_m", "cmd_position_D_init_controller",
    "cmd_position_NE_init_controller"]
  { name := "ground_idle"
    doc := "stock parameters, armed on the ground: make_safe_ground_handling every tick (the \
      controllers initialize themselves at their first update)"
    clauses := own fields (stockAndSignals ++ [fixedOrder fields,
      ⟨"armed_idle", v "armed" ∧. v "interlock" ∧. v "spool_desired" =. 1 ∧.
          v "clear_spoolup_block"⟩,
      -- GUIDED's initialization (pva_control_start) is left out: written as "at the first tick
      -- only" it made the generator skip most cases (one Boolean per command, each tied to the
      -- clock: 13 to 20 of 20 cases skipped). Without it the first NE and D updates initialize
      -- the controllers themselves and raise flow_of_control, which the position stage's
      -- guarantee excludes (no_internal_error_but_flow).
      ⟨"position_no_init", allOf (initCmds.map fun c => ¬. v c)⟩,
      ⟨"position_init_args", v "cmd_position_NE_set_max_speed_accel_m_speed" =. 10 ∧.
          v "cmd_position_NE_set_max_speed_accel_m_accel" =. 2.5 ∧.
          v "cmd_position_NE_set_correction_speed_accel_m_speed" =. 10 ∧.
          v "cmd_position_NE_set_correction_speed_accel_m_accel" =. 2.5 ∧.
          v "cmd_position_D_set_max_speed_accel_m_down" =. 1.5 ∧.
          v "cmd_position_D_set_max_speed_accel_m_up" =. 2.5 ∧.
          v "cmd_position_D_set_max_speed_accel_m_accel" =. 1 ∧.
          v "cmd_position_D_set_correction_speed_accel_m_down" =. 1.5 ∧.
          v "cmd_position_D_set_correction_speed_accel_m_up" =. 2.5 ∧.
          v "cmd_position_D_set_correction_speed_accel_m_accel" =. 1⟩,
      ⟨"position_ground", v "cmd_position_update_estimates" ∧.
          ¬. v "cmd_position_update_estimates_high_vibes" ∧.
          v "cmd_position_NE_relax_velocity_controller" ∧. v "cmd_position_NE_update_controller" ∧.
          v "cmd_position_D_relax_controller" ∧. v "cmd_position_D_relax_controller_throttle" =. 0 ∧.
          v "cmd_position_D_update_controller" ∧.
          othersOff pos (initCmds ++ ["cmd_position_update_estimates",
            "cmd_position_NE_relax_velocity_controller", "cmd_position_NE_update_controller",
            "cmd_position_D_relax_controller", "cmd_position_D_update_controller",
            "cmd_position_set_reset_handling_method"])⟩,
      ⟨"guidance_off", othersOff gd []⟩,
      ⟨"attitude_ground", v "cmd_attitude_reset_rate_controller_I_terms_smoothly" ∧.
          v "cmd_attitude_reset_yaw_target_and_rate" ∧.
          v "cmd_attitude_reset_yaw_target_and_rate_reset_rate" ∧.
          v "cmd_attitude_input_euler_angle_roll_pitch_euler_rate_yaw" ∧.
          v "cmd_attitude_input_euler_angle_roll_pitch_euler_rate_yaw_roll" =. 0 ∧.
          v "cmd_attitude_input_euler_angle_roll_pitch_euler_rate_yaw_pitch" =. 0 ∧.
          v "cmd_attitude_input_euler_angle_roll_pitch_euler_rate_yaw_yaw_rate" =. 0 ∧.
          ¬. v "cmd_attitude_pos_throttle_after_input" ∧.
          v "cmd_attitude_landed_gain_reduction" ∧. v "cmd_attitude_landed_gain_reduction_landed" ∧.
          othersOff att ["cmd_attitude_reset_rate_controller_I_terms_smoothly",
            "cmd_attitude_reset_yaw_target_and_rate",
            "cmd_attitude_input_euler_angle_roll_pitch_euler_rate_yaw",
            "cmd_attitude_landed_gain_reduction", "cmd_attitude_set_throttle_mix_min"]⟩])
    hints := [.increasing "now_ms" 1000 2 3, .increasing "now_us" 1000000 2400 2600] }

/-- What a campaign counts. -/
def coverage : List Clause := [
  ⟨"unlimited", v "spool_state" =. 3⟩,
  ⟨"unlimited_no_limit", v "spool_state" =. 3 ∧. ¬. v "limit_roll" ∧. ¬. v "limit_pitch" ∧.
      ¬. v "limit_yaw" ∧. ¬. v "limit_throttle_lower" ∧. ¬. v "limit_throttle_upper"⟩,
  ⟨"guidance_targets", v "tgt_valid"⟩,
  ⟨"handover_init", v "tgt_ne_init_stopping_point"⟩,
  ⟨"throttle_boosted_above_1", 1 <. v "throttle"⟩,
  ⟨"collective_outside_0_1", v "pc_throttle_set" ∧. (v "throttle_in" <. 0 ∨. 1 <. v "throttle_in")⟩,
  ⟨"rate_reset_i", v "ac_rate_reset_i"⟩]

/-- What the composite assumes about how it is used, for obligations no child's guarantee
implies (`harness obligations ap_ctl --status`):
* `rate_imax_documented`: ATC_RAT_RLL/PIT/YAW_IMAX at most 1, their documented @Range. With it
  rate_pid's `command_magnitude` (|command| ≤ 7e15 + kimax) gives the mixer's
  `commands_bounded` (1e16); rate_pid itself admits any finite kimax.
* `supervisor_limits_in_guidance_range`: the supervisor's NE_ and D_set_max_speed_accel_m
  arguments within what the guidance stage assumes of the position stage's limits
  (`pc_limits_range`), a D argument that is_zero being ignored by the setter. The limits change
  only through those setters (AC_PosControl.cpp:460-461, 810-816) and the guidance stage's
  hand-over, whose values `limits_handed_over` bounds, from the constructor's values
  (`position`'s `withInit`), all within the range.
* `straight_legs_only`: no spline destinations. The guidance stage's targets are bounded on
  straight legs (`targets_bounded_straight`); on spline legs they were refuted (accelerations to
  1524 m/s/s), so the position stage's `tgt_bounded` holds only without them.
* `update_wpnav_last`: when update_wpnav is called, no other guidance command comes after it in
  the supervisor's call order (`_seq`; always so in the fixed order), so that the guidance
  stage's `wp_update_last` holds and its target clauses apply. -/
def usage : List Clause :=
  let v (n : String) : Expr := .var n
  let inR (x : String) (lo hi : Expr) : Expr := lo ≤. v x ∧. v x ≤. hi
  let gd := ["wp_and_spline_init_m", "set_speed_NE_ms", "set_speed_up_ms", "set_speed_down_ms",
    "set_wp_destination_NED_m", "set_spline_destination_NED_m", "set_wp_destination_next_NED_m",
    "set_spline_destination_next_NED_m", "force_stop_at_next_wp", "set_pause", "set_resume"]
  [⟨"rate_imax_documented", v "roll_kimax" ≤. 1 ∧. v "pitch_kimax" ≤. 1 ∧. v "yaw_kimax" ≤. 1⟩,
   ⟨"supervisor_limits_in_guidance_range",
    (¬. v "cmd_position_NE_set_max_speed_accel_m" ∨.
      (inR "cmd_position_NE_set_max_speed_accel_m_speed" 0.01 50 ∧.
       inR "cmd_position_NE_set_max_speed_accel_m_accel" 0.1 20)) ∧.
    (¬. v "cmd_position_D_set_max_speed_accel_m" ∨.
      ((v "cmd_position_D_set_max_speed_accel_m_down" <. 1.1920929e-7 ∨.
        inR "cmd_position_D_set_max_speed_accel_m_down" 0.1 20) ∧.
       (v "cmd_position_D_set_max_speed_accel_m_up" <. 1.1920929e-7 ∨.
        inR "cmd_position_D_set_max_speed_accel_m_up" 0.1 20) ∧.
       (v "cmd_position_D_set_max_speed_accel_m_accel" <. 1.1920929e-7 ∨.
        inR "cmd_position_D_set_max_speed_accel_m_accel" 0.1 20)))⟩,
   ⟨"straight_legs_only", ¬. v "cmd_guidance_set_spline_destination_NED_m" ∧.
      ¬. v "cmd_guidance_set_spline_destination_next_NED_m"⟩,
   ⟨"update_wpnav_last", ¬. v "cmd_guidance_update_wpnav" ∨. allOf (gd.map fun m =>
      v s!"cmd_guidance_{m}_seq" ≤. v "cmd_guidance_update_wpnav_seq")⟩]

/-- How each obligation of the chain is discharged (`harness obligations ap_ctl --status`): the
shared table (ardupilot/harnesses/chain/Discharges.lean), with the gyro bounded by the
composite's assumption `gyro_bounded` (an input here), and the entries citing the usage
assumptions. -/
def discharges : List Discharge :=
  Ardupilot.Harnesses.Chain.discharges (some "assume.gyro_bounded") ++
    Ardupilot.Harnesses.Chain.usage

/-- The position stage's two assumption clauses on the loiter stage's ports: in a chain without
a loiter stage every field they name is a constant (`Position.loiterOffFix`: false, 0), for which
they hold; `obligations` lists a clause fed only by constants all the same. -/
def loiterOffDischarges : List Discharge := [
  { path := "position", clause := "lt_tgt_bounded", kind := "constant",
    note := "every field is the constant 0 (no loiter stage), within the bounds" },
  { path := "position", clause := "lt_handover_args", kind := "constant",
    note := "every field is a constant false or 0 (no loiter stage): each conjunct holds by its \
      false Boolean" }]

/-- The chain with its regimes and coverage. -/
def system (_ : Unit := ()) : Except String Node := do
  let n ← withAssume (← chain) usage
  let n := withDischarges n (discharges ++ loiterOffDischarges)
  let fields := (n.view.params ++ n.view.input).toList.map (·.name)
  let n := withRegime (withRegime n (autoWp fields)) (groundIdle fields)
  return match n with
  | .system s => .system { s with coverage := s.coverage ++ coverage }
  | m => m

end Ardupilot.Harnesses.ApCtl
