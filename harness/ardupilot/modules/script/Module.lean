import Harness.Module
import ardupilot.modules.position.Module
import ardupilot.modules.attitude.Module
import ardupilot.modules.guidance.Module

/-! # script: a TEST DRIVER standing where the supervisor stage will be

**Not part of the flight stack and not ArduPilot code.** A small hand-written module that emits,
from the tick count and the signals it reads back, the arming and spool signals, the clock, and
the commands of one simple flight, in the order ArduCopter's mode code issues them: GUIDED at
boot (ModeGuided::init), arm, a GUIDED takeoff to `sc_takeoff_alt` (Mode::do_user_takeoff_U_m,
ModeGuided::do_user_takeoff_start_m, _AutoTakeoff::run), then AUTO with one waypoint `sc_leg_n`,
`sc_leg_e` north and east of home at the takeoff altitude (ModeAuto::init, do_nav_wp, wp_start,
wp_run), then, the mission complete, AUTO's loiter at the stopping point (exit_mission,
loiter_start, loiter_run). adapter.cpp cites the ArduCopter lines for every call and lists what
the driver leaves out (RC input, the land detector, failsafes, logging, the GCS). The supervisor
stage (ArduCopter's vehicle code, built from the real sources by another agent) replaces it.

Its outputs are every command port of the guidance, position and attitude stages (same names
and types, `_seq` included: all 0, so every stage runs its fixed order), the mixer's arming and
spool inputs, and the clock. -/

namespace Ardupilot.Modules.Script

open Harness Harness.Contract.Lang

private def f (n d : String) : Field := { name := n, type := .f32, doc := d }
private def b (n d : String) : Field := { name := n, type := .bool, doc := d }
private def u (n d : String) : Field := { name := n, type := .u32, doc := d }

def params : Schema := #[
  f "wp_spd" "WP_SPD, m/s: wp_nav->get_default_speed_NE_ms() (ModeGuided::pva_control_start)",
  f "wp_acc" "WP_ACC, m/s/s: get_wp_acceleration_mss()",
  f "wp_spd_up" "WP_SPD_UP, m/s: get_default_speed_up_ms()",
  f "wp_spd_dn" "WP_SPD_DN, m/s: get_default_speed_down_ms()",
  f "wp_acc_z" "WP_ACC_Z, m/s/s: get_accel_D_mss()",
  f "tkoff_slew_time" "TKOFF_SLEW_TIME, s (g2.takeoff_throttle_slew_time)",
  f "tkoff_thr_max" "TKOFF_THR_MAX (g2.takeoff_throttle_max)",
  u "sc_arm_ms" "driver: arm at this time, ms since the start",
  u "sc_takeoff_ms" "driver: the GCS takeoff command at this time, ms since the start",
  f "sc_takeoff_alt" "driver: takeoff altitude above home, m",
  f "sc_leg_n" "driver: the waypoint, m north of home",
  f "sc_leg_e" "driver: the waypoint, m east of home"]

/-- The signals read back (other stages' outputs; the previous tick's where the stage runs
later in the tick). -/
def input : Schema := #[
  u "t_us" "plant_sim: simulated time of this tick's state, us",
  u "spool_state" "mixer: get_spool_state() (previous tick)",
  f "ac_throttle_in" "attitude: get_throttle_in() (previous tick)",
  f "ac_att_target_roll" "attitude: get_att_target_euler_rad().x (previous tick)",
  f "ac_att_target_pitch" "attitude: .y", f "ac_att_target_yaw" "attitude: .z",
  f "ac_thrust_error_angle" "attitude: the thrust error angle, rad (get_att_error_angle_deg)",
  f "pc_pos_desired_d" "position: get_pos_desired_NED_m().z (previous tick)",
  f "pc_vel_desired_d" "position: get_vel_desired_NED_ms().z (previous tick)",
  f "pc_max_speed_up" "position: get_max_speed_up_ms() (previous tick)",
  f "pc_d_max_accel" "position: D_get_max_accel_mss() (previous tick)",
  f "pc_stopping_point_n" "position: get_stopping_point_NE_m().x (previous tick)",
  f "pc_stopping_point_e" "position: .y", f "pc_stopping_point_d" "get_stopping_point_D_m()",
  f "pc_yaw" "position: get_yaw_rad() (previous tick)",
  f "pc_yaw_rate" "position: get_yaw_rate_rads() (previous tick)",
  f "pc_vel_d_control_ratio" "position: get_vel_D_control_ratio() (previous tick)",
  b "wp_reached" "guidance: reached_wp_destination() (previous tick)",
  f "est_pos_d" "estimator: position down from the origin, m",
  f "est_vel_d" "estimator: velocity down, m/s",
  f "est_accel_ef_z" "estimator: get_accel_ef().z, m/s/s"]

/-- Every command port of the three controller stages. -/
def commandPorts : Schema :=
  (Ardupilot.Modules.Guidance.input.filter (·.name.startsWith "cmd_guidance_")) ++
  (Ardupilot.Modules.Position.input.filter (·.name.startsWith "cmd_position_")) ++
  (Ardupilot.Modules.Attitude.input.filter (·.name.startsWith "cmd_attitude_"))

def output : Schema := #[
  f "dt" "set_dt_s: the loop time, s (400 Hz lock-step: 0.0025)",
  u "now_ms" "AP_HAL::millis(): 10 s plus t_us / 1000",
  u "now_us" "AP_HAL::micros(): 10 s plus t_us",
  b "armed" "motors->armed(), AP_Arming_Copter::arm",
  b "interlock" "Copter::motors_output: armed and not in the arming delay (motors.cpp:94)",
  u "spool_desired" "set_desired_spool_state by the mode code",
  b "clear_spoolup_block" "Copter::takeoff_check (50 Hz) clears the spool-up block",
  u "sc_phase" "driver phase: 0 disarmed, 1 armed on the ground, 2 takeoff spooling, 3 takeoff \
    on the ground, 4 takeoff climbing, 5 AUTO waypoint, 6 AUTO loiter",
  b "sc_land_complete" "ap.land_complete as the driver keeps it",
  b "sc_auto_armed" "ap.auto_armed"] ++ commandPorts

private def v (n : String) : Expr := .var n

private def allOf : List Expr → Expr
  | [] => tt
  | [e] => e
  | e :: es => e ∧. allOf es

def contract : Contract where
  assume := [⟨"inputs_finite", allOf ((input.toList.filter (·.type == .f32)).map fun x =>
    finite (v x.name))⟩]
  guarantee := [Ardupilot.Modules.Attitude.singleInput,
    ⟨"dt_400hz", v "dt" =. 0.0025⟩]

def module : Module where
  name := "script"
  doc := "TEST DRIVER standing where the supervisor stage will be: one GUIDED takeoff and AUTO leg"
  params := params
  input := input
  output := output
  contract := contract
  exe := "build/modules/script/script"
  stack := .ardupilot

end Ardupilot.Modules.Script
