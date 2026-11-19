import Harness.Module
import Harness.Compose

/-! # guidance: ArduCopter's waypoint navigator

One `AC_WPNav` (libraries/AC_WPNav/AC_WPNav.cpp) with the trajectory code it owns and calls:
three `SCurve` legs and two `SplineCurve` legs (libraries/AP_Math/SCurve.cpp,
SplineCurve.cpp) and the AP_Math shaping functions (control.cpp). Built as ArduCopter builds it
(Copter::allocate_motors, system.cpp:490-497) and driven by the calls the flight modes make
(mode_auto.cpp, mode_guided.cpp, mode_rtl.cpp, mode_smart_rtl.cpp, mode_zigzag.cpp), then by
`update_wpnav()` once per tick. The executable is built by `ardupilot/build.sh guidance` from the
real, unmodified sources in sources.txt; adapter.cpp is the cut, stubs.cpp (which includes the
stubs_*.cpp files) what is outside.

ArduCopter allocates `AC_WPNav_OA` when AP_OAPATHPLANNER_ENABLED (system.cpp:490). With OA_TYPE
= 0 (the default) `AP_OAPathPlanner::mission_avoidance` returns OA_NOT_REQUIRED
(AP_OAPathPlanner.cpp:207) and every override of AC_WPNav_OA falls through to AC_WPNav, so the
module holds a plain AC_WPNav. AC_Loiter is not in this module (see adapter.cpp).

**Commands.** A command is a Boolean `cmd_guidance_<method>` (the method is called this tick)
and one field per argument. The step runs the commands that are set in this order, the order of
ArduCopter's mode code within a tick, then `update_wpnav()` if `cmd_guidance_update_wpnav`:
1. wp_and_spline_init_m (mode_auto.cpp:477, mode_guided.cpp:214, mode_rtl.cpp:89)
2. set_speed_NE_ms, set_speed_up_ms, set_speed_down_ms (mode_auto.cpp:481-484, 745-759, 2022-2031)
3. set_wp_destination_NED_m, then set_spline_destination_NED_m
4. set_wp_destination_next_NED_m, then set_spline_destination_next_NED_m (mode_auto.cpp:1656-1675)
5. force_stop_at_next_wp (only AC_WPNav_OA calls it; no ArduCopter call site)
6. set_pause, then set_resume (mode_auto.cpp:2436, 2443)
7. update_wpnav (mode_auto.cpp:1146, mode_guided.cpp:242, mode_rtl.cpp:272, …)

The `_loc` forms (set_wp_destination_loc, set_wp_destination_next_loc,
set_spline_destination_loc, set_spline_destination_next_loc) convert a Location to NED meters
from the EKF origin (AC_WPNav::get_vector_NED_m) and call the `_NED_m` form. Here the supervisor
does that conversion (it holds the EKF origin) and sends the `_NED_m` command. Terrain is out of
scope: every `is_terrain_alt` argument is false (alt-above-origin frames only), so the terrain
branches of the code are not reached (stubs_terrain.cpp aborts if they are).

**The position controller is another stage.** Every `_pos_control.` call is either a signal read
from the position stage (inputs `pc_…`, its outputs of the previous tick; `est_…` for the
position and velocity estimates, which AC_PosControl::update_estimates copies from the AHRS at
the start of the tick, inertia.cpp:7) or a call handed to it (outputs `tgt_…`, applied by the
position stage in the same tick, after this module). stubs_posctl.cpp lists every call and what
it became. -/

namespace Ardupilot.Modules.Guidance

open Harness Harness.Contract.Lang

def params : Schema := #[
  { name := "wp_spd", type := .f32, doc := "WP_SPD, m/s (_wp_speed_ms)" },
  { name := "wp_radius_m", type := .f32, doc := "WP_RADIUS_M, m (_wp_radius_m)" },
  { name := "wp_spd_up", type := .f32, doc := "WP_SPD_UP, m/s (_wp_speed_up_ms)" },
  { name := "wp_spd_dn", type := .f32, doc := "WP_SPD_DN, m/s (_wp_speed_down_ms)" },
  { name := "wp_acc", type := .f32, doc := "WP_ACC, m/s/s (_wp_accel_mss)" },
  { name := "wp_acc_z", type := .f32, doc := "WP_ACC_Z, m/s/s (_wp_accel_z_mss)" },
  { name := "wp_acc_cnr", type := .f32,
    doc := "WP_ACC_CNR, m/s/s, 0 = 2 WP_ACC (_wp_accel_c_mss)" },
  { name := "wp_jerk", type := .f32, doc := "WP_JERK, m/s/s/s (_wp_jerk_msss)" },
  { name := "wp_ter_margin", type := .f32, doc := "WP_TER_MARGIN, m (_terrain_margin_m)" },
  { name := "atc_rate_r_max", type := .f32,
    doc := "ATC_RATE_R_MAX, deg/s (AC_AttitudeControl::_ang_vel_roll_max_degs)" },
  { name := "atc_rate_p_max", type := .f32,
    doc := "ATC_RATE_P_MAX, deg/s (AC_AttitudeControl::_ang_vel_pitch_max_degs)" },
  { name := "atc_input_tc", type := .f32,
    doc := "ATC_INPUT_TC, s (AC_AttitudeControl::_input_tc)" },
  { name := "atc_acc_r_max", type := .f32,
    doc := "ATC_ACC_R_MAX, deg/s/s (AC_AttitudeControl::_accel_roll_max_degss)" },
  { name := "atc_acc_p_max", type := .f32,
    doc := "ATC_ACC_P_MAX, deg/s/s (AC_AttitudeControl::_accel_pitch_max_degss)" },
  { name := "psc_ne_pos_p", type := .f32,
    doc := "PSC_NE_POS_P (AC_PosControl::NE_get_pos_p().kP(), read by the track scaler)" },
  { name := "psc_ne_jerk", type := .f32,
    doc := "PSC_NE_JERK, m/s/s/s (AC_PosControl::get_shaping_jerk_NE_msss())" }]

/-- `cmd_guidance_<method>`, its doc. -/
def cmd (method doc : String) : Field :=
  { name := s!"cmd_guidance_{method}", type := .bool, doc }

/-- `cmd_guidance_<method>_<arg>`. -/
def arg (method a : String) (t : FieldType) (doc : String) : Field :=
  { name := s!"cmd_guidance_{method}_{a}", type := t, doc }

/-- The three components of a NED vector argument. -/
def arg3 (method a doc : String) : List Field :=
  ["n", "e", "d"].map fun c => arg method s!"{a}_{c}" .f32 s!"{doc}, {c.toUpper}, m"

def inputBase : Schema := #[
  { name := "dt", type := .f32, doc := "AC_PosControl::get_dt_s(): the loop period, s" },
  { name := "now_ms", type := .u32,
    doc := "the clock AP_HAL::millis() reads (is_active, wp_and_spline_init_m, update_wpnav)" },
  { name := "est_pos_n", type := .f32,
    doc := "AC_PosControl::get_pos_estimate_NED_m().x: position estimate from the EKF origin, m" },
  { name := "est_pos_e", type := .f32, doc := "get_pos_estimate_NED_m().y, m" },
  { name := "est_pos_d", type := .f32, doc := "get_pos_estimate_NED_m().z, m" },
  { name := "est_vel_n", type := .f32, doc := "get_vel_estimate_NED_ms().x, m/s" },
  { name := "est_vel_e", type := .f32, doc := "get_vel_estimate_NED_ms().y, m/s" },
  { name := "est_vel_d", type := .f32, doc := "get_vel_estimate_NED_ms().z, m/s" },
  { name := "pc_vel_desired_n", type := .f32,
    doc := "AC_PosControl::get_vel_desired_NED_ms().x after the previous tick's update, m/s" },
  { name := "pc_vel_desired_e", type := .f32, doc := "get_vel_desired_NED_ms().y, m/s" },
  { name := "pc_vel_desired_d", type := .f32, doc := "get_vel_desired_NED_ms().z, m/s" },
  { name := "pc_vel_offset_d", type := .f32, doc := "AC_PosControl::get_vel_offset_D_ms(), m/s" },
  { name := "pc_pos_offset_n", type := .f32, doc := "AC_PosControl::get_pos_offset_NED_m().x, m" },
  { name := "pc_pos_offset_e", type := .f32, doc := "get_pos_offset_NED_m().y, m" },
  { name := "pc_pos_offset_d", type := .f32, doc := "get_pos_offset_NED_m().z, m" },
  { name := "pc_pos_error_n", type := .f32,
    doc := "AC_PosControl::get_pos_error_NED_m().x (the NE P controller's error), m" },
  { name := "pc_pos_error_e", type := .f32, doc := "get_pos_error_NED_m().y, m" },
  { name := "pc_pos_error_d", type := .f32,
    doc := "get_pos_error_NED_m().z (the D P controller), m" },
  { name := "pc_pos_target_d", type := .f32,
    doc := "AC_PosControl::_pos_target_ned_m.z (read by terrain_scaler_D_m), m" },
  { name := "pc_stopping_point_n", type := .f32,
    doc := "AC_PosControl::get_stopping_point_NE_m().x, m" },
  { name := "pc_stopping_point_e", type := .f32, doc := "get_stopping_point_NE_m().y, m" },
  { name := "pc_stopping_point_d", type := .f32,
    doc := "AC_PosControl::get_stopping_point_D_m(), m" },
  { name := "pc_ne_max_speed", type := .f32, doc := "AC_PosControl::NE_get_max_speed_ms(), m/s" },
  { name := "pc_ne_max_accel", type := .f32,
    doc := "AC_PosControl::NE_get_max_accel_mss(), m/s/s" },
  { name := "pc_max_speed_up", type := .f32, doc := "AC_PosControl::get_max_speed_up_ms(), m/s" },
  { name := "pc_max_speed_down", type := .f32,
    doc := "AC_PosControl::get_max_speed_down_ms(), m/s" },
  { name := "pc_d_max_accel", type := .f32, doc := "AC_PosControl::D_get_max_accel_mss(), m/s/s" },
  cmd "wp_and_spline_init_m" "AC_WPNav::wp_and_spline_init_m(speed_ms, stopping_point_ned_m)",
  arg "wp_and_spline_init_m" "speed_ms" .f32 "speed_ms, m/s (0: WP_SPD)"] ++
  (arg3 "wp_and_spline_init_m" "stopping_point" "stopping_point_ned_m (all 0: the stopping point)"
    ).toArray ++ #[
  cmd "set_speed_NE_ms" "AC_WPNav::set_speed_NE_ms(speed_ms)",
  arg "set_speed_NE_ms" "speed_ms" .f32 "speed_ms, m/s",
  cmd "set_speed_up_ms" "AC_WPNav::set_speed_up_ms(speed_up_ms)",
  arg "set_speed_up_ms" "speed_up_ms" .f32 "speed_up_ms, m/s",
  cmd "set_speed_down_ms" "AC_WPNav::set_speed_down_ms(speed_down_ms)",
  arg "set_speed_down_ms" "speed_down_ms" .f32 "speed_down_ms, m/s",
  cmd "set_wp_destination_NED_m"
    "AC_WPNav::set_wp_destination_NED_m(destination_ned_m, false, arc_rad); also the _loc form"] ++
  (arg3 "set_wp_destination_NED_m" "destination" "destination_ned_m").toArray ++ #[
  arg "set_wp_destination_NED_m" "arc_rad" .f32 "arc_rad, rad (0: straight leg)",
  cmd "set_spline_destination_NED_m"
    "AC_WPNav::set_spline_destination_NED_m(destination, false, next_destination, false, \
      next_is_spline); also the _loc form"] ++
  (arg3 "set_spline_destination_NED_m" "destination" "destination_ned_m").toArray ++
  (arg3 "set_spline_destination_NED_m" "next_destination" "next_destination_ned_m").toArray ++ #[
  arg "set_spline_destination_NED_m" "next_is_spline" .bool "next_is_spline",
  cmd "set_wp_destination_next_NED_m"
    "AC_WPNav::set_wp_destination_next_NED_m(destination_ned_m, false, arc_rad); also _loc"] ++
  (arg3 "set_wp_destination_next_NED_m" "destination" "destination_ned_m").toArray ++ #[
  arg "set_wp_destination_next_NED_m" "arc_rad" .f32 "arc_rad, rad",
  cmd "set_spline_destination_next_NED_m"
    "AC_WPNav::set_spline_destination_next_NED_m(next_destination, false, \
      next_next_destination, false, next_next_is_spline); also the _loc form"] ++
  (arg3 "set_spline_destination_next_NED_m" "next_destination" "next_destination_ned_m"
    ).toArray ++
  (arg3 "set_spline_destination_next_NED_m" "next_next_destination" "next_next_destination_ned_m"
    ).toArray ++ #[
  arg "set_spline_destination_next_NED_m" "next_next_is_spline" .bool "next_next_is_spline",
  cmd "force_stop_at_next_wp" "AC_WPNav::force_stop_at_next_wp()",
  cmd "set_pause" "AC_WPNav::set_pause()",
  cmd "set_resume" "AC_WPNav::set_resume()",
  cmd "update_wpnav" "AC_WPNav::update_wpnav(): the per-tick update"]

/-- One `cmd_guidance_<method>_seq` (u32) per command method: the position of this call in the supervisor's call order within the tick, counting from 1 across all stages; 0 = not sequenced (all 0: the stage's fixed order). Set commands
run in increasing `_seq` (a set command with `_seq` 0 in a sequenced tick runs after the
sequenced commands that precede it in the fixed order); with every `_seq` 0, in the fixed order
of the header. -/
def seqFields : Schema :=
  (inputBase.filter fun f => f.type == .bool && f.name.startsWith "cmd_guidance_" &&
    (f.doc.startsWith "AC_WPNav::")).map fun f =>
    { name := s!"{f.name}_seq", type := .u32, doc := s!"{f.name}: call order in the tick" }

def input : Schema := inputBase ++ seqFields

def output : Schema := #[
  { name := "tgt_handover_seq", type := .u32,
    doc := "the `_seq` of this tick's first command that called the position controller's \
      initializers or limit setters (wp_and_spline_init_m, set_speed_*, a re-initializing \
      set_wp_destination_NED_m); 0 if none was sequenced: where the position stage runs the \
      hand-over" },
  { name := "tgt_update_seq", type := .u32,
    doc := "the `_seq` of the command that called set_pos_vel_accel_NED_m and \
      NE_update_controller (update_wpnav); 0 if not sequenced" },
  { name := "tgt_pos_n", type := .f32,
    doc := "set_pos_vel_accel_NED_m pos_ned_m.x (double, rounded to binary32), m" },
  { name := "tgt_pos_e", type := .f32, doc := "pos_ned_m.y, m" },
  { name := "tgt_pos_d", type := .f32, doc := "pos_ned_m.z, m" },
  { name := "tgt_vel_n", type := .f32, doc := "set_pos_vel_accel_NED_m vel_ned_ms.x, m/s" },
  { name := "tgt_vel_e", type := .f32, doc := "vel_ned_ms.y, m/s" },
  { name := "tgt_vel_d", type := .f32, doc := "vel_ned_ms.z, m/s" },
  { name := "tgt_acc_n", type := .f32, doc := "set_pos_vel_accel_NED_m accel_ned_mss.x, m/s/s" },
  { name := "tgt_acc_e", type := .f32, doc := "accel_ned_mss.y, m/s/s" },
  { name := "tgt_acc_d", type := .f32, doc := "accel_ned_mss.z, m/s/s" },
  { name := "tgt_valid", type := .bool,
    doc := "set_pos_vel_accel_NED_m(tgt_pos, tgt_vel, tgt_acc) then NE_update_controller() \
      were called this tick (update_wpnav ran); the tgt_pos/vel/acc fields are 0 otherwise" },
  { name := "tgt_ne_init_stopping_point", type := .bool,
    doc := "AC_PosControl::NE_init_controller_stopping_point() called this tick" },
  { name := "tgt_d_init_stopping_point", type := .bool,
    doc := "AC_PosControl::D_init_controller_stopping_point() called this tick" },
  { name := "tgt_ne_set_max_speed_accel", type := .bool,
    doc := "NE_set_max_speed_accel_m(tgt_ne_max_speed, tgt_ne_max_accel) called this tick" },
  { name := "tgt_ne_max_speed", type := .f32,
    doc := "_vel_max_ne_ms after this tick's calls (pc_ne_max_speed if none), m/s" },
  { name := "tgt_ne_max_accel", type := .f32,
    doc := "_accel_max_ne_mss after this tick's calls (pc_ne_max_accel if none), m/s/s" },
  { name := "tgt_ne_set_correction_speed_accel", type := .bool,
    doc := "NE_set_correction_speed_accel_m(tgt_ne_correction_speed, …_accel) called" },
  { name := "tgt_ne_correction_speed", type := .f32, doc := "its last speed argument, m/s" },
  { name := "tgt_ne_correction_accel", type := .f32, doc := "its last accel argument, m/s/s" },
  { name := "tgt_d_set_max_speed_accel", type := .bool,
    doc := "D_set_max_speed_accel_m(tgt_max_speed_down, tgt_max_speed_up, tgt_d_max_accel) \
      called this tick" },
  { name := "tgt_max_speed_down", type := .f32,
    doc := "_vel_max_down_ms after this tick's calls (pc_max_speed_down if none), m/s" },
  { name := "tgt_max_speed_up", type := .f32,
    doc := "_vel_max_up_ms after this tick's calls (pc_max_speed_up if none), m/s" },
  { name := "tgt_d_max_accel", type := .f32,
    doc := "_accel_max_d_mss after this tick's calls (pc_d_max_accel if none), m/s/s" },
  { name := "tgt_d_set_correction_speed_accel", type := .bool,
    doc := "D_set_correction_speed_accel_m(down, up, accel) called this tick" },
  { name := "tgt_d_correction_speed_down", type := .f32, doc := "its last descent speed, m/s" },
  { name := "tgt_d_correction_speed_up", type := .f32, doc := "its last climb speed, m/s" },
  { name := "tgt_d_correction_accel", type := .f32, doc := "its last accel argument, m/s/s" },
  { name := "wp_reached", type := .bool, doc := "AC_WPNav::reached_wp_destination()" },
  { name := "wp_distance", type := .f32,
    doc := "get_wp_distance_to_destination_m(): horizontal, from est_pos, m" },
  { name := "wp_bearing", type := .f32,
    doc := "get_wp_bearing_to_destination_rad(): from est_pos, rad, 0 = North" },
  { name := "wp_active", type := .bool, doc := "AC_WPNav::is_active() at now_ms" },
  { name := "wp_paused", type := .bool, doc := "AC_WPNav::paused()" },
  { name := "wp_update_last", type := .bool,
    doc := "update_wpnav ran this tick as the last command (always so in the fixed order)" },
  { name := "wp_update_ok", type := .bool,
    doc := "update_wpnav()'s result (false only on missing terrain data; true if not run)" },
  { name := "wp_origin_n", type := .f32, doc := "get_wp_origin_NED_m().x (double), m" },
  { name := "wp_origin_e", type := .f32, doc := "get_wp_origin_NED_m().y, m" },
  { name := "wp_origin_d", type := .f32, doc := "get_wp_origin_NED_m().z, m" },
  { name := "wp_destination_n", type := .f32, doc := "get_wp_destination_NED_m().x (double), m" },
  { name := "wp_destination_e", type := .f32, doc := "get_wp_destination_NED_m().y, m" },
  { name := "wp_destination_d", type := .f32, doc := "get_wp_destination_NED_m().z, m" },
  { name := "wp_fast", type := .bool,
    doc := "_flags.fast_waypoint: a next leg is set and the leg will not stop (contract)" },
  { name := "wp_leg_spline", type := .bool, doc := "_this_leg_is_spline (contract)" },
  { name := "wp_leg_arc", type := .bool,
    doc := "_scurve_this_leg's is_arc_segment: an ARC_WAYPOINT leg (contract)" },
  { name := "wp_prev_leg_finished", type := .bool,
    doc := "_scurve_prev_leg.finished(): no blending from the previous leg (contract)" },
  { name := "wp_leg_peak_speed", type := .f32,
    doc := "_scurve_this_leg: the largest end speed of its segments (its planned peak speed \
      along the track), 0 for a zero-length leg, m/s (contract)" },
  { name := "wp_leg_vel_max", type := .f32,
    doc := "_scurve_this_leg.vel_max: the speed limit along the track it was last planned for, \
      m/s (contract)" },
  { name := "wp_leg_accel_max", type := .f32,
    doc := "_scurve_this_leg.accel_max: its acceleration limit along the track, m/s/s \
      (contract)" },
  { name := "wp_speed_ne", type := .f32,
    doc := "_wp_desired_speed_ne_ms: the leg's horizontal speed, m/s (contract)" },
  { name := "wp_offset_vel", type := .f32,
    doc := "_offset_vel_ms: the shaped speed that scales the track time, m/s (contract)" },
  { name := "wp_offset_accel", type := .f32,
    doc := "_offset_accel_mss: the speed shaper's acceleration, m/s/s (contract)" },
  { name := "wp_track_dt_scalar", type := .f32, doc := "_track_dt_scalar (contract)" },
  { name := "wp_internal_errors", type := .u32,
    doc := "ArduPilot internal errors raised since init" },
  { name := "wp_internal_errors_uninit", type := .u32,
    doc := "of these, the errors raised while the navigator had never been initialized \
      (_scurve_jerk_max_msss and _scurve_snap_max_mssss still 0: before the first \
      wp_and_spline_init_m)" },
  { name := "wp_internal_errors_incoherent", type := .u32,
    doc := "of the others, the errors raised once wp_limits_incoherent was set" },
  { name := "wp_limits_incoherent", type := .bool,
    doc := "the position stage has returned (pc_ne_max_speed … pc_d_max_accel) other limits than \
      the module handed it at the tick before (tgt_ne_max_speed … tgt_d_max_accel), at some tick \
      since init: harness bookkeeping (adapter.cpp), not ArduPilot state" }]

/-! ### Clause builders -/

/-- The f32 outputs, all finite. -/
def outputsFinite : Expr :=
  (output.toList.filter (·.type == .f32)).foldr (fun f acc => finite (.var f.name) ∧. acc)
    (finite "wp_distance")

def bounded (f : String) (b : Expr) : Expr := abs (.var f) ≤. b

def bounded3 (pre : String) (b : Expr) : Expr :=
  bounded s!"{pre}_n" b ∧. bounded s!"{pre}_e" b ∧. bounded s!"{pre}_d" b

def inRange (f : String) (lo hi : Expr) : Expr := lo ≤. .var f ∧. .var f ≤. hi

/-! ### Assumption -/

/-- The parameters' documented ranges (@Range in AC_WPNav.cpp:24-110, AC_AttitudeControl.cpp,
AC_PosControl.cpp). WP_ACC_CNR may be 0 (its default: twice WP_ACC). The attitude limits are
narrowed below (`assumeAtcCorrected`). -/
def assumeParamsDocumented : List Clause := [
  ⟨"wp_spd_range", 0.1 ≤. "wp_spd" ∧. "wp_spd" ≤. 20⟩,
  ⟨"wp_radius_range", 0.05 ≤. "wp_radius_m" ∧. "wp_radius_m" ≤. 10⟩,
  ⟨"wp_spd_up_range", 0.1 ≤. "wp_spd_up" ∧. "wp_spd_up" ≤. 10⟩,
  ⟨"wp_spd_dn_range", 0.1 ≤. "wp_spd_dn" ∧. "wp_spd_dn" ≤. 10⟩,
  ⟨"wp_acc_range", 0.5 ≤. "wp_acc" ∧. "wp_acc" ≤. 5⟩,
  ⟨"wp_acc_z_range", 0.5 ≤. "wp_acc_z" ∧. "wp_acc_z" ≤. 5⟩,
  ⟨"wp_acc_cnr_range", 0 ≤. "wp_acc_cnr" ∧. "wp_acc_cnr" ≤. 5⟩,
  ⟨"wp_jerk_range", 1 ≤. "wp_jerk" ∧. "wp_jerk" ≤. 20⟩,
  ⟨"wp_ter_margin_range", 0.1 ≤. "wp_ter_margin" ∧. "wp_ter_margin" ≤. 100⟩,
  ⟨"atc_input_tc_range", 0 ≤. "atc_input_tc" ∧. "atc_input_tc" ≤. 1⟩,
  ⟨"psc_ne_pos_p_range", 0.5 ≤. "psc_ne_pos_p" ∧. "psc_ne_pos_p" ≤. 4⟩,
  ⟨"psc_ne_jerk_range", 1 ≤. "psc_ne_jerk" ∧. "psc_ne_jerk" ≤. 50⟩]

/-- The attitude limits as first stated: their documented ranges, ATC_RATE_R/P_MAX in [0, 1080]
deg/s and ATC_ACC_R/P_MAX in [0, 1800] deg/s/s. Refuted (seed 1, 100 x 100): a tiny positive
ATC_ACC_P_MAX (around 1e-38) passes is_positive after radians() and GRAVITY_MSS and makes the
S-curve snap limit tiny (calc_scurve_jerk_and_snap, AC_WPNav.cpp:1085-1088); the segment
durations overflow to ∞ and SCurve::generate_path raises invalid_arg_or_result (SCurve.cpp:232).
A tiny ATC_RATE_R/P_MAX does the same through the jerk limit (AC_WPNav.cpp:1073-1077). The
second statement, 0 or at least 1 deg/s/s, was refuted too: ATC_ACC_R_MAX = 1 with WP_JERK 19.9
gives a snap limit 0.09 and a raised-cosine jerk time of 364 s, and a 7 mm leg overflowed the
same way (SCurve.cpp:232). Kept for the record, not used. -/
def assumeAtcAsFirstStated : List Clause := [
  ⟨"atc_rate_range", inRange "atc_rate_r_max" 0 1080 ∧. inRange "atc_rate_p_max" 0 1080⟩,
  ⟨"atc_acc_range", inRange "atc_acc_r_max" 0 1800 ∧. inRange "atc_acc_p_max" 0 1800⟩]

/-- The attitude limits: 0 (disabled) or at least the slowest setting ArduPilot lists in @Values
(ATC_RATE_R/P_MAX 60 "Slow", ATC_ACC_R/P_MAX 300 "VerySlow", AC_AttitudeControl.cpp:97, 188). -/
def assumeAtcCorrected : List Clause := [
  ⟨"atc_rate_range", ("atc_rate_r_max" =. 0 ∨. inRange "atc_rate_r_max" 60 1080) ∧.
      ("atc_rate_p_max" =. 0 ∨. inRange "atc_rate_p_max" 60 1080)⟩,
  ⟨"atc_acc_range", ("atc_acc_r_max" =. 0 ∨. inRange "atc_acc_r_max" 300 1800) ∧.
      ("atc_acc_p_max" =. 0 ∨. inRange "atc_acc_p_max" 300 1800)⟩]

/-- The signals: positions within 1 km of the EKF origin, speeds within 50 m/s, the position
controller's limits positive (it never holds a zero limit: its constructor sets them, and
D_set_max_speed_accel_m ignores 0), the loop period of a 50 Hz to 10 kHz loop. -/
def assumeSignals : List Clause := [
  ⟨"dt_range", inRange "dt" 0.0001 0.02⟩,
  ⟨"est_bounded", bounded3 "est_pos" 1000 ∧. bounded3 "est_vel" 50⟩,
  ⟨"pc_signals_bounded", bounded3 "pc_vel_desired" 50 ∧. bounded "pc_vel_offset_d" 50 ∧.
      bounded3 "pc_pos_offset" 100 ∧. bounded3 "pc_pos_error" 1000 ∧.
      bounded "pc_pos_target_d" 1000 ∧. bounded3 "pc_stopping_point" 1000⟩,
  ⟨"pc_limits_range", inRange "pc_ne_max_speed" 0.01 50 ∧. inRange "pc_ne_max_accel" 0.1 20 ∧.
      inRange "pc_max_speed_up" 0.1 20 ∧. inRange "pc_max_speed_down" 0.1 20 ∧.
      inRange "pc_d_max_accel" 0.1 20⟩,
  ⟨"cmd_init_args", inRange "cmd_guidance_wp_and_spline_init_m_speed_ms" 0 50 ∧.
      bounded3 "cmd_guidance_wp_and_spline_init_m_stopping_point" 1000⟩]

def destinationsBounded : Expr :=
  bounded3 "cmd_guidance_set_wp_destination_NED_m_destination" 1000 ∧.
  bounded3 "cmd_guidance_set_wp_destination_next_NED_m_destination" 1000 ∧.
  bounded3 "cmd_guidance_set_spline_destination_NED_m_destination" 1000 ∧.
  bounded3 "cmd_guidance_set_spline_destination_NED_m_next_destination" 1000 ∧.
  bounded3 "cmd_guidance_set_spline_destination_next_NED_m_next_destination" 1000 ∧.
  bounded3 "cmd_guidance_set_spline_destination_next_NED_m_next_next_destination" 1000

/-- The command arguments as first stated: speeds anywhere in [0, 50] horizontally and [0, 20]
vertically, arc angles within ±6.3 rad (ARC_WAYPOINT). Refuted twice:
* set_speed_up_ms(2.1e-7) (seed 2, 100 x 100): 2.1e-7 is not is_zero, so the stand-in, like
  D_set_max_speed_accel_m (AC_PosControl.cpp:812), stores it; update_track_with_speed_accel_limits
  replans the climbing leg for a climb rate of 2.1e-7 m/s and SCurve::set_speed_max finds the
  path invalid (SCurve.cpp:437). A climb or descent speed between FLT_EPSILON and 0.1 m/s is
  below WP_SPD_UP/WP_SPD_DN's documented minimum.
* an arc leg with a horizontal chord between FLT_EPSILON and about 2 FLT_EPSILON
  (ardupilot/modules/guidance/arc-radius-case.json, from seed 6): SCurve::calculate_track takes the arc
  branch (chord is_positive) but the radius chord / (2 |sin(angle/2)|) is below FLT_EPSILON and
  project_scurve_onto_track raises invalid_arg_or_result (SCurve.cpp:678-683). The arc's origin
  is the previous destination, which no assumption over one tick can see, so arc legs are
  excluded (arc_rad = 0); the arc code is compiled and reachable but not covered.
Kept for the record, not used. -/
def assumeCommandsAsFirstStated : List Clause := [
  ⟨"cmd_speed_args", inRange "cmd_guidance_set_speed_NE_ms_speed_ms" 0 50 ∧.
      inRange "cmd_guidance_set_speed_up_ms_speed_up_ms" 0 20 ∧.
      inRange "cmd_guidance_set_speed_down_ms_speed_down_ms" 0 20⟩,
  ⟨"cmd_destination_args", destinationsBounded ∧.
      bounded "cmd_guidance_set_wp_destination_NED_m_arc_rad" 6.3 ∧.
      bounded "cmd_guidance_set_wp_destination_next_NED_m_arc_rad" 6.3⟩]

/-- The command arguments: a climb or descent speed is 0 (ignored) or at least 0.1 m/s; legs are
straight (arc_rad = 0). -/
def assumeCommands : List Clause := [
  ⟨"cmd_speed_args", inRange "cmd_guidance_set_speed_NE_ms_speed_ms" 0 50 ∧.
      ("cmd_guidance_set_speed_up_ms_speed_up_ms" =. 0 ∨.
        inRange "cmd_guidance_set_speed_up_ms_speed_up_ms" 0.1 20) ∧.
      ("cmd_guidance_set_speed_down_ms_speed_down_ms" =. 0 ∨.
        inRange "cmd_guidance_set_speed_down_ms_speed_down_ms" 0.1 20)⟩,
  ⟨"cmd_destination_args", destinationsBounded ∧.
      "cmd_guidance_set_wp_destination_NED_m_arc_rad" =. 0 ∧.
      "cmd_guidance_set_wp_destination_next_NED_m_arc_rad" =. 0⟩]

/-! ### Guarantee -/

/-- A straight S-curve leg flown on its own: update_wpnav ran, the leg is neither a spline nor an
arc, no next leg is set (so no corner blending into it) and the previous leg's blending is over. -/
def straightLeg : Expr :=
  "tgt_valid" ∧. ¬. "wp_leg_spline" ∧. ¬. "wp_leg_arc" ∧. ¬. "wp_fast" ∧.
    "wp_prev_leg_finished"

/-- The speed shaper settled: at or below the desired speed and not accelerating, so the track
time and the target velocity are scaled by at most 1 and get no acceleration offset
(AC_WPNav.cpp:594-633). -/
def shaperSettled : Expr :=
  "wp_offset_vel" ≤. "wp_speed_ne" ∧. "wp_offset_accel" =. 0

def dot (a b : String → Expr) : Expr := a "n" * b "n" + a "e" * b "e" + a "d" * b "d"
def sumSq (f : String → Expr) (cs : List String) : Expr :=
  cs.foldl (fun acc c => acc + f c * f c) 0
def org (c : String) : Expr := .var s!"wp_origin_{c}"
def dst (c : String) : Expr := .var s!"wp_destination_{c}"
def tpos (c : String) : Expr := .var s!"tgt_pos_{c}"
def tvel (c : String) : Expr := .var s!"tgt_vel_{c}"
def tacc (c : String) : Expr := .var s!"tgt_acc_{c}"

/-- The distance from the target position to the segment from origin to destination is at most
`tol`, without a square root: with u = destination - origin, w = target - origin, q = target -
destination, either the target projects before the origin and |w| ≤ tol, or past the
destination and |q| ≤ tol, or onto the segment and |w × u| ≤ tol |u|. -/
def nearSegment (tol : Expr) : Expr :=
  let u := fun c => dst c - org c
  let w := fun c => tpos c - org c
  let q := fun c => tpos c - dst c
  let wu := dot w u
  let uu := dot u u
  let cx := w "e" * u "d" - w "d" * u "e"
  let cy := w "d" * u "n" - w "n" * u "d"
  let cz := w "n" * u "e" - w "e" * u "n"
  (wu ≤. 0 ∧. dot w w ≤. tol * tol) ∨. (uu ≤. wu ∧. dot q q ≤. tol * tol) ∨.
    (0 ≤. wu ∧. wu ≤. uu ∧. cx * cx + cy * cy + cz * cz ≤. tol * tol * uu)

/-- FLT_EPSILON: AC_WPNav scales the track time by _offset_vel_ms / _wp_desired_speed_ne_ms only
when the desired speed is_positive (≥ FLT_EPSILON), AC_WPNav.cpp:594-600. -/
def fltEps : Expr := 1.1920929e-7

/-- |tgt_vel|² ≤ (planned peak × speed scalar)² × `rel`, without a division: the speed scalar is
wp_offset_vel / wp_speed_ne when wp_speed_ne ≥ FLT_EPSILON, else 1. -/
def speedWithinPlan (rel : Expr) : Expr :=
  let vv := dot tvel tvel
  let pk := "wp_leg_peak_speed"
  ("wp_speed_ne" <. fltEps ∧. vv ≤. pk * pk * rel) ∨.
    (fltEps ≤. "wp_speed_ne" ∧.
      vv * ("wp_speed_ne" * "wp_speed_ne") ≤. pk * pk * ("wp_offset_vel" * "wp_offset_vel") * rel)

/-- The tolerance of the position clauses: positions are within 2 km of each other (assumption)
and are rounded from double to binary32 on output (half an ulp at 1000 m is 3.1e-5 m); the
S-curve's along-track position and its direction are binary32 (relative error a few 1e-7, so a
few 1e-4 m at 2 km). 1 cm is more than an order of magnitude above both. -/
def posTol : Expr := 0.01

/-- The guarantee.
* `speed_within_plan`: the S-curve speed lies between the end speeds of its segment (the
  acceleration keeps its sign within a segment), so it is at most the planned peak; the target
  velocity is that speed along a unit direction times the shaper's scalar (AC_WPNav.cpp:631).
  Tolerance 2e-5 on the squares: binary32 rounding of the segment formulas and of the unit
  vector (the stock straight leg reaches 10.000001 m/s against a planned peak of 10).
* `speed_within_limits`, `accel_within_limits`: with the shaper settled the scalar is at most 1;
  a straight leg's plan never exceeds the horizontal and vertical limits it was planned or
  replanned with (kinematic_limit, control.cpp:756), and those come from pc_ne_max_speed and
  the commands (≤ 50 m/s horizontally, ≤ 20 m/s vertically by the assumption). Its accelerations
  are planned with WP_ACC and WP_ACC_Z (calculate_track's accel arguments are the parameters,
  AC_WPNav.cpp:421) and are never replanned (SCurve.cpp:255). Tolerances 2e-5 and 1e-5
  relative, as above. -/
def guarantee : List Clause := [
  ⟨"outputs_finite", outputsFinite⟩,
  ⟨"no_internal_error_initialized", "wp_internal_errors" =.
      "wp_internal_errors_uninit" + "wp_internal_errors_incoherent"⟩,
  ⟨"on_segment", ¬. straightLeg ∨. nearSegment posTol⟩,
  ⟨"reached_holds", ¬. ("tgt_valid" ∧. "wp_reached" ∧. ¬. "wp_fast" ∧. ¬. "wp_leg_spline") ∨.
      (abs (tpos "n" - dst "n") ≤. posTol ∧. abs (tpos "e" - dst "e") ≤. posTol ∧.
        abs (tpos "d" - dst "d") ≤. posTol)⟩,
  ⟨"speed_within_plan", ¬. straightLeg ∨. speedWithinPlan 1.00002⟩,
  ⟨"speed_within_limits", ¬. (straightLeg ∧. "wp_offset_vel" ≤. "wp_speed_ne") ∨.
      (sumSq tvel ["n", "e"] ≤. 2500.05 ∧. abs (tvel "d") ≤. 20.0002)⟩,
  ⟨"accel_within_limits", ¬. (straightLeg ∧. shaperSettled) ∨.
      (sumSq tacc ["n", "e"] ≤. "wp_acc" * "wp_acc" * 1.00002 ∧.
        abs (tacc "d") ≤. "wp_acc_z" * 1.00001)⟩,
  ⟨"limits_handed_over", inRange "tgt_ne_max_speed" 0.01 50 ∧.
      inRange "tgt_ne_max_accel" 0.1 20 ∧. inRange "tgt_max_speed_up" 0.1 20 ∧.
      inRange "tgt_max_speed_down" 0.1 20 ∧. inRange "tgt_d_max_accel" 0.1 20⟩]

/-- The guarantee as first stated: no internal error at all. Refuted at once (seed 1, 100 x 100,
case 2 step 0): before the first wp_and_spline_init_m the S-curve snap and jerk limits are 0
(they are set only by calc_scurve_jerk_and_snap, AC_WPNav.cpp:241), so a next-leg setter
(set_wp_destination_next_NED_m, AC_WPNav.cpp:495) builds a leg with snap 0 and
SCurve::generate_path raises invalid_arg_or_result (SCurve.cpp:219). ArduCopter's modes always
initialize first (set_wp_destination_NED_m re-initializes by itself when inactive or not reached,
AC_WPNav.cpp:386), but the next-leg setters do not, and an assumption over one tick cannot say
"after an initialization". The stub now classifies each error (wp_internal_errors_uninit) and the
guarantee states that every internal error was raised before the first initialization.

That second statement (wp_internal_errors = wp_internal_errors_uninit) was refuted too (seed 2,
200 x 500, case 144 step 379): the leg had been planned for a horizontal speed of 3.42 m/s, the
position stage then returned pc_ne_max_speed = 0.01, and a set_speed_down_ms in the same tick
replanned the leg in its acceleration phase for 0.01 m/s; SCurve::set_speed_max found no room to
decelerate and calculate_path raised invalid_arg_or_result (SCurve.cpp:955). With the position
stage returning the limits it was handed, the same inputs raise no error (checked by rerunning
the case with pc_ limits = the previous tick's tgt_ limits). The limits are a signal of the
position stage of the previous tick, and its obligation to return them unchanged cannot be said
over one tick, so the adapter records it (wp_limits_incoherent) and the guarantee states that
every internal error came before the first initialization or after such a tick. -/
def guaranteeAsFirstStated : List Clause :=
  ⟨"no_internal_error", "wp_internal_errors" =. 0⟩ :: guarantee.filter
    (·.name != "no_internal_error_initialized")

/-- Clauses refuted on the way, kept for the record, not used:
* `reached_holds` for every leg, splines included: refuted (seed 1, 100 x 300, case 44 step 273;
  ardupilot/modules/guidance/spline-reached-case.json): SplineCurve advances its time by distance / spline
  speed, and near the start of a spline that leaves from rest the spline speed is tiny; a jump of
  the desired velocity the position stage reports (pc_vel_desired) makes the step exceed the
  whole spline, so the leg reports reached while that tick's target is still at the origin.
* `plan_within_limit` (wp_leg_peak_speed ≤ wp_leg_vel_max): refuted (seed 1, 100 x 300, case 7
  step 2, and in every seed): when a lower limit arrives during the acceleration phase,
  SCurve::set_speed_max keeps the speed already committed (Vmin, SCurve.cpp:338-345), so the plan
  exceeds the new limit. The limits clause is therefore stated against the configured envelope.
* `offset_vel_within_desired` (0 ≤ wp_offset_vel ≤ wp_speed_ne): refuted (seed 2, 100 x 300,
  case 93 step 53: -0.0236 with a desired speed of 0.0517): set_speed_NE_ms scales
  _offset_vel_ms by the ratio of the speeds but keeps _offset_accel_mss (AC_WPNav.cpp:283), and
  the jerk-limited shaper overshoots by up to a²/(2 PSC_NE_JERK).
* `speed_within_limits` unconditional (a straight leg's horizontal target speed within the
  limits): refuted by a closed-loop scenario with a coherent, ideal position stage
  (ardupilot/modules/guidance/scenarios.py, case build/guidance/speed-overshoot-case.json): after
  set_pause, set_resume and set_speed_NE_ms(0.1) the target speed is 6.27 m/s with WP_SPD 5
  (20.8 m/s with stock WP_SPD 10): the shaper's overshoot times the committed S-curve speed. The
  clause now requires the shaper at or below the desired speed. -/
def guaranteeRefuted : List Clause := [
  ⟨"reached_holds_all_legs", ¬. ("tgt_valid" ∧. "wp_reached" ∧. ¬. "wp_fast") ∨.
      (abs (tpos "n" - dst "n") ≤. posTol ∧. abs (tpos "e" - dst "e") ≤. posTol ∧.
        abs (tpos "d" - dst "d") ≤. posTol)⟩,
  ⟨"plan_within_limit", "wp_leg_peak_speed" ≤. "wp_leg_vel_max" * 1.00001⟩,
  ⟨"offset_vel_within_desired", 0 ≤. "wp_offset_vel" ∧.
      "wp_offset_vel" ≤. "wp_speed_ne" * 1.00001 + 0.000001⟩,
  ⟨"speed_within_limits_as_first_stated", ¬. straightLeg ∨.
      (sumSq tvel ["n", "e"] ≤. 2500.05 ∧. abs (tvel "d") ≤. 20.0002)⟩]

/-- The contract of the stage as built alone. Not refuted; two guarantee clauses were added
when the stages were composed. Kept for the record, not used. -/
def contractAlone : Contract where
  assume := assumeParamsDocumented ++ assumeAtcCorrected ++ assumeSignals ++ assumeCommands
  guarantee := guarantee

/-- Added when the stages were composed, for the position stage's assumptions on what this
stage hands it:
* `corrections_handed_over`: the arguments of NE_ and D_set_correction_speed_accel_m, when
  called, within [0, 100] (the position stage's `tgt_handover_args`). They are
  _wp_desired_speed_ne_ms and WP_ACC, WP_SPD_DN, WP_SPD_UP and WP_ACC_Z (AC_WPNav.cpp:233, 235,
  290), each bounded by the assumption.
* `targets_bounded_straight`: on a leg that is not a spline, |tgt_pos| ≤ 1e4 m, |tgt_vel| ≤
  100 m/s, |tgt_acc| ≤ 100 m/s/s (the position stage's `tgt_bounded`). Tested, not derived.
  First stated for every leg (`targetsBoundedAsFirstStated`), refuted at once (seed 1, 200 x 100:
  34 steps, accelerations to 1524 m/s/s and speeds to 96 m/s; seed 2, 100 x 300: 78 steps,
  first at case 12 step 30): every counterexample is a spline leg (wp_leg_spline) whose
  planned peak speed is 0 while the shaped speed is 0.01 m/s; SplineCurve advances by distance
  over its own speed (see guaranteeRefuted's `reached_holds_all_legs`), and a jump of the
  reported desired velocity moves the target far along the spline in one tick. The position
  stage's `tgt_bounded` is therefore open for spline legs. -/
def targetsBoundedAsFirstStated : Clause :=
  ⟨"targets_bounded", bounded3 "tgt_pos" 10000 ∧. bounded3 "tgt_vel" 100 ∧.
      bounded3 "tgt_acc" 100⟩

def guaranteeComposed : List Clause := guarantee ++ [
  ⟨"corrections_handed_over",
    (¬. "tgt_ne_set_correction_speed_accel" ∨. (inRange "tgt_ne_correction_speed" 0 100 ∧.
        inRange "tgt_ne_correction_accel" 0 100)) ∧.
    (¬. "tgt_d_set_correction_speed_accel" ∨. (inRange "tgt_d_correction_speed_down" 0 100 ∧.
        inRange "tgt_d_correction_speed_up" 0 100 ∧. inRange "tgt_d_correction_accel" 0 100))⟩,
  ⟨"targets_bounded_straight", "wp_leg_spline" ∨. (bounded3 "tgt_pos" 10000 ∧.
      bounded3 "tgt_vel" 100 ∧. bounded3 "tgt_acc" 100)⟩]

/-- The guarantee with the supervisor's call order (`_seq`). In the fixed order update_wpnav is
the last command of the tick, so `tgt_valid` (it ran) describes the targets of the leg the
outputs describe. With random `_seq` (seed 11, 100 x 300) on_segment failed at 1149 steps,
reached_holds 1627, speed_within_plan 1291, speed_within_limits 456, accel_within_limits 226,
targets_bounded_straight 49 and outputs_finite 1 (stock_leg seed 12: on_segment 10,
reached_holds 5, speed_within_plan 5): a destination or init command after update_wpnav
replaces the leg the targets were computed on. Restated: the leg clauses (through
`straightLeg`) and `reached_holds` and `targets_bounded_straight` also require `wp_update_last`.
`outputs_finite` (case 97 step 5: NaN accelerations, only update_wpnav called that tick) failed
on a spline leg set up in an earlier sequenced tick before the navigator's first
wp_and_spline_init_m (wp_internal_errors_uninit = 3: the S-curve and spline limits still 0);
restated as finite unless such an error was raised (`0 < wp_internal_errors_uninit`). -/
def guaranteeSeq : List Clause :=
  guaranteeComposed.map fun c =>
    let last (e : Expr) : Expr := e.mapVars fun x => if x == "tgt_valid" then
      .and (.var "tgt_valid") (.var "wp_update_last") else .var x
    if c.name == "outputs_finite" then ⟨c.name, 0 <. "wp_internal_errors_uninit" ∨. c.expr⟩
    else if c.name == "targets_bounded_straight" then ⟨c.name, ¬. "wp_update_last" ∨. c.expr⟩
    else if ["on_segment", "reached_holds", "speed_within_plan", "speed_within_limits",
             "accel_within_limits"].contains c.name then ⟨c.name, last c.expr⟩
    else c

def contract : Contract where
  assume := assumeParamsDocumented ++ assumeAtcCorrected ++ assumeSignals ++ assumeCommands
  guarantee := guaranteeSeq

/-! ### Regimes and coverage (they steer and measure campaigns; the contract is above) -/

def cmdOff (m : String) : Expr := ¬. (.var s!"cmd_guidance_{m}")

/-- One straight leg from rest: at the first tick (now_ms = 1000) wp_and_spline_init_m (speed
0: WP_SPD; stopping point 0: the position stage's) and set_wp_destination_NED_m, then only
update_wpnav, every tick, at 400 Hz. -/
def legClauses : List Clause := [
  ⟨"leg_start", ("now_ms" ≤. 1000 ∧. "cmd_guidance_wp_and_spline_init_m" ∧.
      "cmd_guidance_set_wp_destination_NED_m") ∨.
    (1000 <. "now_ms" ∧. cmdOff "wp_and_spline_init_m" ∧. cmdOff "set_wp_destination_NED_m")⟩,
  ⟨"leg_only", cmdOff "set_spline_destination_NED_m" ∧. cmdOff "set_wp_destination_next_NED_m" ∧.
      cmdOff "set_spline_destination_next_NED_m" ∧. cmdOff "force_stop_at_next_wp" ∧.
      cmdOff "set_pause" ∧. cmdOff "set_resume" ∧. cmdOff "set_speed_NE_ms" ∧.
      cmdOff "set_speed_up_ms" ∧. cmdOff "set_speed_down_ms" ∧. "cmd_guidance_update_wpnav"⟩,
  ⟨"leg_init_args", "cmd_guidance_wp_and_spline_init_m_speed_ms" =. 0 ∧.
      "cmd_guidance_wp_and_spline_init_m_stopping_point_n" =. 0 ∧.
      "cmd_guidance_wp_and_spline_init_m_stopping_point_e" =. 0 ∧.
      "cmd_guidance_wp_and_spline_init_m_stopping_point_d" =. 0⟩,
  ⟨"leg_400hz", inRange "dt" 0.0024 0.0026⟩]

def legHints : List Hint := [.increasing "now_ms" 1000 2 3]

def leg : Regime where
  name := "leg"
  doc := "one straight leg from rest, documented parameter ranges, random signals"
  clauses := legClauses ++ [⟨"leg_geometry", bounded3 "pc_stopping_point" 100 ∧.
      bounded3 "cmd_guidance_set_wp_destination_NED_m_destination" 100⟩]
  hints := legHints

/-- One straight leg of 3.6 m from (0, 0, -10) to (3, -2, -10) with the vehicle already at the
destination, at rest, and the position controller without error or offset: the track scaler is
1, the leg finishes in a few seconds (WP_SPD at least 1 m/s) and is then reached. -/
def legArrive : Regime where
  name := "leg_arrive"
  doc := "one 3.6 m straight leg flown to the end and reached"
  clauses := legClauses ++ [
    ⟨"arrive_geometry", "pc_stopping_point_n" =. 0 ∧. "pc_stopping_point_e" =. 0 ∧.
      "pc_stopping_point_d" =. -10 ∧. "cmd_guidance_set_wp_destination_NED_m_destination_n" =. 3 ∧.
      "cmd_guidance_set_wp_destination_NED_m_destination_e" =. -2 ∧.
      "cmd_guidance_set_wp_destination_NED_m_destination_d" =. -10⟩,
    ⟨"arrive_vehicle", "est_pos_n" =. 3 ∧. "est_pos_e" =. -2 ∧. "est_pos_d" =. -10 ∧.
      "est_vel_n" =. 0 ∧. "est_vel_e" =. 0 ∧. "est_vel_d" =. 0⟩,
    ⟨"arrive_position_stage", "pc_vel_desired_n" =. 0 ∧. "pc_vel_desired_e" =. 0 ∧.
      "pc_vel_desired_d" =. 0 ∧. "pc_vel_offset_d" =. 0 ∧. "pc_pos_offset_n" =. 0 ∧.
      "pc_pos_offset_e" =. 0 ∧. "pc_pos_offset_d" =. 0 ∧. "pc_pos_error_n" =. 0 ∧.
      "pc_pos_error_e" =. 0 ∧. "pc_pos_error_d" =. 0 ∧. "pc_pos_target_d" =. -10⟩,
    ⟨"arrive_speed", 1 ≤. "wp_spd"⟩]
  hints := legHints

/-- ArduCopter's default parameters: WP_SPD 10, WP_RADIUS_M 2, WP_SPD_UP 2.5, WP_SPD_DN 1.5,
WP_ACC 2.5, WP_ACC_Z 1, WP_ACC_CNR 0, WP_JERK 1, WP_TER_MARGIN 10 (AC_WPNav.cpp:8-14, 37, 45,
92, 110; AC_WPNav.h:15); ATC_RATE_R/P_MAX 0, ATC_INPUT_TC 0.1 (Copter, AC_AttitudeControl.cpp:16,
104, 114, 134), ATC_ACC_R/P_MAX 1100 (AC_AttitudeControl.h:22); PSC_NE_POS_P 1 (Copter,
AC_PosControl.cpp:63), PSC_NE_JERK 5 (AC_PosControl.h:20). -/
def stockParams : List Clause := [
  ⟨"stock_wp", "wp_spd" =. 10 ∧. "wp_radius_m" =. 2 ∧. "wp_spd_up" =. 2.5 ∧.
      "wp_spd_dn" =. 1.5 ∧. "wp_acc" =. 2.5 ∧. "wp_acc_z" =. 1 ∧. "wp_acc_cnr" =. 0 ∧.
      "wp_jerk" =. 1 ∧. "wp_ter_margin" =. 10⟩,
  ⟨"stock_atc", "atc_rate_r_max" =. 0 ∧. "atc_rate_p_max" =. 0 ∧. "atc_input_tc" =. 0.1 ∧.
      "atc_acc_r_max" =. 1100 ∧. "atc_acc_p_max" =. 1100⟩,
  ⟨"stock_psc", "psc_ne_pos_p" =. 1 ∧. "psc_ne_jerk" =. 5⟩]

def stockLeg : Regime where
  name := "stock_leg"
  doc := "ArduCopter's default parameters, one straight leg from rest, random signals"
  clauses := stockParams ++ leg.clauses
  hints := legHints

def stockArrive : Regime where
  name := "stock_arrive"
  doc := "ArduCopter's default parameters, the 3.6 m leg of leg_arrive flown to the end"
  clauses := stockParams ++ legArrive.clauses.filter (·.name != "arrive_speed")
  hints := legHints

/-- What a campaign counts. -/
def coverage : List Clause := [
  ⟨"straight_leg", straightLeg⟩,
  ⟨"straight_settled", straightLeg ∧. shaperSettled⟩,
  ⟨"straight_moving", straightLeg ∧. 0.1 ≤. sumSq tvel ["n", "e", "d"]⟩,
  ⟨"reached_scurve", "tgt_valid" ∧. "wp_reached" ∧. ¬. "wp_fast" ∧. ¬. "wp_leg_spline"⟩,
  ⟨"spline_leg", "tgt_valid" ∧. "wp_leg_spline"⟩,
  ⟨"blending", "tgt_valid" ∧. ("wp_fast" ∨. ¬. "wp_prev_leg_finished")⟩,
  ⟨"shaper_active", "tgt_valid" ∧. ¬. shaperSettled⟩]

def module : Module where
  name := "guidance"
  doc := "ArduCopter's AC_WPNav with its S-curve and spline legs, stepped by update_wpnav()"
  params := params
  input := input
  output := output
  contract := contract
  exe := "build/modules/guidance/guidance"
  stack := .ardupilot
  regimes := [leg, legArrive, stockLeg, stockArrive]
  coverage := coverage

end Ardupilot.Modules.Guidance
