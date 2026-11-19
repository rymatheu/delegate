import Harness.Compose
import ardupilot.harnesses.ap_ctl.Composed
import sim.modules.plant_sim.Module
import ardupilot.modules.truth_est.Module
import ardupilot.modules.script.Module

/-! # ap_flight: the controller chain flown in the simulator

`composeAll [plant_sim, truth_est, script, rate_c, mixer, guidance, position, attitude]`: the
gorge simulator's X500, a STAND-IN for the estimator (`truth_est`: the true state under the
estimator's names), a TEST DRIVER where the supervisor will be (`script`: one GUIDED takeoff to
2 m and an AUTO leg of 10 m north, then a hold), and ArduCopter's real controllers. The
simulator's PWM fields are renamed to the mixer's (`pwm0` … `pwm3` ← `pwm_1` … `pwm_4`, one tick
late, 1000 at the first tick), as in closed_inner.

Parameters: ArduCopter's defaults for every stage, and the X500's values where the simulator's
parameter list (sim/params/storage-x500.txt of the ArduLean simulator, read only) differs:
MOT_THST_EXPO 0, MOT_SPIN_ARM 0, MOT_SPIN_MIN 0, MOT_SPIN_MAX 1, MOT_THST_HOVER 0.3835 (with
MOT_HOVER_LEARN 0, so the hover throttle the mixer reports to the position and attitude stages
is that parameter; the driver issues no motor calls: output_min, update_throttle_hover and
set_thrust_boost are fixed off), the autotuned ATC_ angle and rate gains and
acceleration limits, ATC_RAT_YAW_* and ATC_ACC_Y_MAX as changed there, PSC_D_ACC_P 0.03,
PSC_D_ACC_I 0.06, WP_SPD 2. They are fixed (`fix`), so the composite has no parameter but the
simulator's noise switch and seed. The mixer's PWM range is 1000 to 2000 with PWM kept while
disarmed (MOT_SAFE_DISARM 0), so that the simulator's `pwm_range` can be discharged. The battery
readings are fixed at 0 (none): with MOT_BAT_VOLT_MAX = 0 and MOT_BAT_CURR_MAX = 0 the mixer
reads neither. The feed-forward inputs of the mixer are 0 (ATC_RAT_*_FF = 0). -/

namespace Ardupilot.Harnesses.ApFlight

open Harness Harness.Contract.Lang

/-- The node without its regimes (they steer sampling only; a stage's stock regimes contradict
the X500's constants, and `fix` refuses a regime its constants violate). -/
def noRegimes : Node → Node
  | .module m => .module { m with regimes := [] }
  | .system s => .system { s with regimes := [] }

/-- The constants of `vals` that are fields of `n` (parameters or inputs), fixed. -/
def fixOwn (n : Node) (vals : List (String × Word)) : Except String Node :=
  let names := (n.view.params ++ n.view.input).toList.map (·.name)
  fix (noRegimes n) (vals.filter fun (f, _) => names.contains f)

/-- Every parameter of the flight, by its shared name. -/
def x500 : List (String × Word) :=
  let rate (a : String) (kp ki kd fe fd : Float32) : List (String × Word) :=
    [(s!"{a}_kp", .f32 kp), (s!"{a}_ki", .f32 ki), (s!"{a}_kd", .f32 kd),
     (s!"{a}_kimax", .f32 0.5), (s!"{a}_kpdmax", .f32 0), (s!"{a}_filt_T_hz", .f32 21),
     (s!"{a}_filt_E_hz", .f32 fe), (s!"{a}_filt_D_hz", .f32 fd), (s!"{a}_slew_max", .f32 0)]
  rate "roll" 0.1255951 0.1255951 0.004905871 0 21 ++
  rate "pitch" 0.1466683 0.1466683 0.005201788 0 21 ++
  rate "yaw" 0.78 0.078 0.0144 2.5 10 ++ [
  -- mixer (MOT_*)
  ("spin_min", .f32 0), ("spin_max", .f32 1), ("spin_arm", .f32 0), ("thst_expo", .f32 0),
  ("thst_hover", .f32 0.3835), ("yaw_headroom", .i32 200), ("pwm_min", .i32 1000),
  ("pwm_max", .i32 2000), ("bat_volt_max", .f32 0), ("bat_volt_min", .f32 0),
  ("bat_curr_max", .f32 0), ("bat_curr_tc", .f32 5), ("spool_time", .f32 0.5),
  ("spool_tim_dn", .f32 0), ("slew_up_time", .f32 0), ("slew_dn_time", .f32 0),
  ("safe_disarm", .bool false), ("safe_time", .f32 1), ("idle_sec", .f32 0),
  ("hover_learn", .i32 0), ("cmd_mixer_output_min", .bool false),
  ("cmd_mixer_set_thrust_boost", .bool false), ("cmd_mixer_set_thrust_boost_enable", .bool false),
  ("cmd_mixer_update_throttle_hover", .bool false), ("cmd_mixer_update_throttle_hover_dt", .f32 0),
  ("origin_lat_e7", .i32 388405556), ("origin_lon_e7", .i32 (-1050441667)),
  ("origin_alt_cm", .i32 430200),
  -- attitude (ATC_*)
  ("atc_rate_ff_enab", .bool true), ("atc_angle_boost", .bool true),
  ("atc_ang_rll_p", .f32 26.35878), ("atc_ang_pit_p", .f32 21.2236), ("atc_ang_yaw_p", .f32 3),
  ("atc_ang_lim_tc", .f32 1), ("atc_rate_r_max", .f32 0), ("atc_rate_p_max", .f32 0),
  ("atc_rate_y_max", .f32 0), ("atc_input_tc", .f32 0.1), ("atc_land_r_mult", .f32 1),
  ("atc_land_p_mult", .f32 1), ("atc_land_y_mult", .f32 1), ("atc_angle_max", .f32 30),
  ("atc_rate_wpy_max", .f32 60), ("atc_acc_y_max", .f32 90), ("atc_acc_r_max", .f32 1767.26),
  ("atc_acc_p_max", .f32 1651.67), ("atc_thr_mix_min", .f32 0.1), ("atc_thr_mix_max", .f32 0.5),
  ("atc_thr_mix_man", .f32 0.1), ("atc_thr_g_boost", .f32 0),
  -- position (PSC_*)
  ("psc_ne_pos_p", .f32 1), ("psc_d_pos_p", .f32 1), ("psc_ne_vel_p", .f32 2),
  ("psc_ne_vel_i", .f32 1), ("psc_ne_vel_d", .f32 0.25), ("psc_ne_vel_imax", .f32 10),
  ("psc_ne_vel_flte", .f32 5), ("psc_ne_vel_fltd", .f32 5), ("psc_ne_vel_ff", .f32 0),
  ("psc_d_vel_p", .f32 5), ("psc_d_vel_i", .f32 0), ("psc_d_vel_d", .f32 0),
  ("psc_d_vel_imax", .f32 10), ("psc_d_vel_flte", .f32 5), ("psc_d_vel_fltd", .f32 5),
  ("psc_d_vel_ff", .f32 0), ("psc_d_acc_p", .f32 0.03), ("psc_d_acc_i", .f32 0.06),
  ("psc_d_acc_d", .f32 0), ("psc_d_acc_imax", .f32 0.8), ("psc_d_acc_ff", .f32 0),
  ("psc_d_acc_fltt", .f32 0), ("psc_d_acc_flte", .f32 20), ("psc_d_acc_fltd", .f32 0),
  ("psc_d_acc_smax", .f32 0), ("psc_d_acc_pdmx", .f32 0), ("psc_d_acc_d_ff", .f32 0),
  ("psc_angle_max", .f32 0), ("psc_ne_jerk", .f32 5), ("psc_d_jerk", .f32 5),
  -- guidance (WP_*)
  ("wp_spd", .f32 2), ("wp_radius_m", .f32 2), ("wp_spd_up", .f32 2.5), ("wp_spd_dn", .f32 1.5),
  ("wp_acc", .f32 2.5), ("wp_acc_z", .f32 1), ("wp_acc_cnr", .f32 0), ("wp_jerk", .f32 1),
  ("wp_ter_margin", .f32 10),
  -- the test driver (TKOFF_* defaults, Parameters.cpp:978, 1057) and its flight
  ("tkoff_slew_time", .f32 2), ("tkoff_thr_max", .f32 0.9), ("sc_arm_ms", .u32 500),
  ("sc_takeoff_ms", .u32 3000), ("sc_takeoff_alt", .f32 2), ("sc_leg_n", .f32 10),
  ("sc_leg_e", .f32 0),
  -- inputs nothing produces
  ("roll_ff", .f32 0), ("pitch_ff", .f32 0), ("yaw_ff", .f32 0),
  ("batt_voltage", .f32 0), ("batt_resting_voltage", .f32 0), ("batt_current", .f32 0),
  ("batt_current_ok", .bool false), ("batt_resistance", .f32 0)]

/-- The simulator with its PWM inputs named as the mixer's outputs. -/
def plant (_ : Unit := ()) : Except String Node :=
  rename (.module Sim.Modules.PlantSim.module)
    [("pwm0", "pwm_1"), ("pwm1", "pwm_2"), ("pwm2", "pwm_3"), ("pwm3", "pwm_4")]

/-- The mixer, its PWMs 1000 before the first step (the simulator reads them at the first
tick). -/
def mixer (_ : Unit := ()) : Except String Node := do
  let m ← fixOwn (.module Ardupilot.Modules.Mixer.module) x500
  withInit m [("pwm_1", .u32 1000), ("pwm_2", .u32 1000), ("pwm_3", .u32 1000),
    ("pwm_4", .u32 1000)]

private def v (f : String) : Expr := .var f

/-- No sensor noise (truth_est copies the truth, so noise changes only the gyro). -/
def quiet : Regime where
  name := "quiet"
  doc := "no sensor noise"
  clauses := [⟨"no_noise", v "noise_on" =. ff ∧. v "noise_seed" =. 0⟩]

def noisy : Regime where
  name := "noisy"
  doc := "the simulator's sensor noise, seed 1"
  clauses := [⟨"noise", v "noise_on" =. tt ∧. v "noise_seed" =. 1⟩]

def system (_ : Unit := ()) : Except String Node := do
  let n ← composeAll "ap_flight" [← plant,
    ← fixOwn (.module Ardupilot.Modules.TruthEst.module) x500,
    ← fixOwn (.module Ardupilot.Modules.Script.module) x500,
    ← fixOwn (← Ardupilot.Harnesses.RateC.system) x500, ← mixer,
    ← fixOwn (.module Ardupilot.Modules.Guidance.module) x500,
    ← fixOwn (← Ardupilot.Harnesses.ApCtl.position) x500, ← fixOwn (← Ardupilot.Harnesses.ApCtl.attitude) x500]
  -- the chain's shared table: nothing here bounds `truth_est`'s gyro, and ATC_THR_G_BOOST is a
  -- constant (x500)
  return withDischarges (withRegime (withRegime n quiet) noisy)
    (Ardupilot.Harnesses.ApCtl.loiterOffDischarges ++
      Ardupilot.Harnesses.Chain.discharges none (boost := none))

end Ardupilot.Harnesses.ApFlight
