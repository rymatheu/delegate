import Harness.Compose
import ardupilot.harnesses.rate.Composed
import ardupilot.harnesses.ap_ctl.Composed
import sim.modules.plant_sim.Module
import ardupilot.modules.truth_est.Module
import ardupilot.modules.mixer.Module
import ardupilot.modules.supervisor.Module
import ardupilot.modules.guidance.Module
import ardupilot.modules.loiter.Module

/-! # ap_full: the whole ArduCopter stack around the simulator

`plant_sim → truth_est → rate_c → mixer → supervisor → guidance → loiter → position → attitude`,
the brief's tick order with the loiter stage (AC_Loiter, ardupilot/modules/loiter) beside the
guidance stage, composed by port name. `truth_est` stands for the estimator stage (the
simulator's truth under the estimator's names, ardupilot/modules/truth_est). The supervisor reads the
estimator, rate and mixer outputs of the same tick and the guidance, position and attitude
outputs of the previous tick (`prev`); its arming, spool and command fields feed the mixer
(previous tick: the mixer runs before it, as Copter's motors_output runs before
update_flight_mode) and the controllers (same tick). The inputs of the composite are time, the
pilot's RC channels and the ground-station bytes.

Fixed here: the mixer's feed-forward inputs (0: the rate PIDs' FF gains are 0), its battery
readings (no battery is simulated: constant 24 V, 10 A, 0.02 ohm, inside the mixer's stock
regime; with the stock MOT_BAT_VOLT_MAX = 0 and MOT_BAT_CURR_MAX = 0 they change nothing), and
the position stage's two inputs nothing produces (ApCtl.positionOpen), and the loiter stage's
estimator ground-speed limit, which `truth_est` does not report (`loiter`). The PWMs start at
1000. -/

namespace Ardupilot.Harnesses.ApFull

open Harness

/-- The plant with its PWM inputs named as the mixer's outputs (motors 1..4 = slots 0..3). -/
def plant (_ : Unit := ()) : Except String Node :=
  rename (.module Sim.Modules.PlantSim.module)
    [("pwm0", "pwm_1"), ("pwm1", "pwm_2"), ("pwm2", "pwm_3"), ("pwm3", "pwm_4")]

/-- The mixer, as described above. -/
def mixer (_ : Unit := ()) : Except String Node := do
  let m ← fix (.module Ardupilot.Modules.Mixer.module)
    [("roll_ff", .f32 0), ("pitch_ff", .f32 0), ("yaw_ff", .f32 0),
     ("batt_voltage", .f32 24), ("batt_resting_voltage", .f32 24), ("batt_current", .f32 10),
     ("batt_current_ok", .bool true), ("batt_resistance", .f32 0.02)]
  withInit m [("pwm_1", .u32 1000), ("pwm_2", .u32 1000), ("pwm_3", .u32 1000),
    ("pwm_4", .u32 1000)]

/-- The attitude stage of ap_ctl, with one more value before its first step, read by the
supervisor at the first tick: the target quaternion of a fresh controller, identity
(AC_AttitudeControl's _attitude_target default-constructed, Quaternion() = (1, 0, 0, 0)). -/
def attitude (_ : Unit := ()) : Except String Node := do
  withInit (← Ardupilot.Harnesses.ApCtl.attitude) [("ac_att_target_q1", .f32 1)]

/-- The position stage of ap_ctl with the loiter stage's ports open (ApCtl.positionOpen) and its
two commands no covered flow makes fixed off: the supervisor's own set_pos_desired_NE_m (only
AC_Loiter::init_target_m calls it, AC_Loiter.cpp:131, which is the loiter stage's
`lt_cmd_position_set_pos_desired_NE_m`) and set_reset_handling_method (an inline setter at
Copter::set_mode, not detected yet). -/
def position (_ : Unit := ()) : Except String Node := do
  fix (← Ardupilot.Harnesses.ApCtl.positionOpen)
    [("cmd_position_set_pos_desired_NE_m", .bool false),
     ("cmd_position_set_pos_desired_NE_m_n", .f32 0),
     ("cmd_position_set_pos_desired_NE_m_e", .f32 0),
     ("cmd_position_set_pos_desired_NE_m_seq", .u32 0),
     ("cmd_position_set_reset_handling_method", .bool false),
     ("cmd_position_set_reset_handling_method_method", .u32 0),
     ("cmd_position_set_reset_handling_method_seq", .u32 0)]

/-- The loiter stage with the value its `lt_angle_max` has before its first step, which the
supervisor reads at the first tick (`prev`): get_angle_max_rad() with ArduCopter's defaults,
2/3 of radians(ATC_ANGLE_MAX = 30) (LOIT_ANG_MAX = 0, PSC_ANGLE_MAX = 0; AC_Loiter.cpp:237-239).
A constant: with other parameters the first tick sees the default's value (no mode reads it at
boot). -/
def loiterInit (_ : Unit := ()) : Except String Node :=
  withInit (.module Ardupilot.Modules.Loiter.module) [("lt_angle_max", .f32 0.34906584)]

/-- The loiter stage with the estimator's ground-speed limit fixed at EKF3's value when it does
not rely on optical flow, 400 m/s (AP_NavEKF3_Outputs.cpp:390): `truth_est` stands for the
estimator and does not report it (ap_full_ekf wires the real estimator's `est_gnd_spd_limit`). -/
def loiter (_ : Unit := ()) : Except String Node := do
  fix (← loiterInit) [("est_gnd_spd_limit", .f32 400)]

/-- The supervisor (it reads the mixer's `throttle_hover`; it no longer outputs one). -/
def supervisor (_ : Unit := ()) : Except String Node := pure (.module Ardupilot.Modules.Supervisor.module)

/-- How the obligations on the loiter stage's wires are discharged, or that they are open
(`harness obligations ap_full --status`; ap_full_ekf adds the estimator's ground-speed limit).
The other obligations of this composite have no stated discharge yet. -/
def loiterDischarges : List Discharge := [
  { path := "loiter", clause := "pc_lean_range", kind := "guarantee",
    by_ := ["position.lean_limit_range"],
    note := "[1, 80] deg from the position stage (previous tick) within [0, 80] deg; before the \
      position stage's first step the wire holds 0, also within" },
  { path := "loiter", clause := "ac_att_target_range", kind := "guarantee",
    by_ := ["attitude.att_target_euler_range"],
    note := "the attitude target's roll and pitch within ±π (previous tick; 0 before its first step)" },
  { path := "loiter", clause := "est_yaw_range", kind := "hypothesis",
    note := "the estimator stage states its yaw only finite (as for the position stage's \
      est_yaw_range); AP_AHRS's yaw comes from to_euler (atan2), within ±π, not a clause yet" },
  { path := "loiter", clause := "pc_signals_bounded", kind := "hypothesis",
    note := "the position stage guarantees its desired velocity and position, acceleration \
      target, attitude targets and stopping point only finite; bounding them is a statement about \
      the closed-loop flight envelope (as the guidance stage's pc_signals_bounded in ap_ctl)" },
  { path := "loiter", clause := "pilot_angles_range", kind := "hypothesis",
    note := "the supervisor's mode code limits the pilot's lean angles to get_angle_max_rad() = \
      lt_angle_max ≤ 80 deg · 2/3 or LOIT_ANG_MAX ≤ 45 deg (get_pilot_desired_lean_angles_rad, \
      mode.cpp; ModeLoiter::run, mode_loiter.cpp:87-90): below 1 rad; the supervisor's contract \
      does not state it" },
  { path := "loiter", clause := "init_target_m_range", kind := "hypothesis",
    note := "init_target_m's position comes from the position estimate minus the offset \
      (mode_poshold.cpp:421) or a ZigZag destination (mode_zigzag.cpp:239); LOITER does not call \
      it; not stated by the supervisor" },
  { path := "loiter", clause := "speed_max_range", kind := "hypothesis",
    note := "set_speed_max_NE_ms is the tuning knob's (tuning.cpp:214), not used in these flights" },
  { path := "position", clause := "lt_handover_args", kind := "hypothesis",
    note := "the limit parts follow from the loiter stage's guarantees handover_constants and \
      accel_max_bounded (correction speed 2, error limit 2, correction acceleration = \
      lt_accel_max in (0, LOIT_ACC_MAX_M ≤ 9.81], loit_range being a parameter clause of the \
      composite); the desired-position part is init_target_m's argument \
      (pos_desired_from_init_target_m), bounded only by the loiter stage's own open assumption \
      init_target_m_range (above), so the clause as a whole is not implied" },
  { path := "position", clause := "lt_tgt_bounded", kind := "hypothesis",
    note := "implied by the loiter stage's guarantees under ModeLoiter's call order: \
      vel_within_speed_limit (|v| ≤ max(min(LOIT_SPEED_MS ≤ 35, EKF limit), 0.2) when update is \
      the last loiter command of the tick), accel_bounded (each component ≤ 60 when \
      set_pilot_desired_acceleration_rad precedes update in the tick), pos_follows_vel (the \
      previous desired position plus v·dt, bounded by its open pc_signals_bounded); that order \
      (mode_loiter.cpp:90, 139, 160) is the supervisor's, stated by no guarantee" }]

/-- The full stack. -/
def system (_ : Unit := ()) : Except String Node := do
  composeAll "ap_full" [← plant, .module Ardupilot.Modules.TruthEst.module, ← Ardupilot.Harnesses.RateC.system,
    ← mixer, ← supervisor, .module Ardupilot.Modules.Guidance.module, ← loiter,
    ← position, ← attitude] >>= fun n =>
    -- with the chain's shared table; nothing here bounds `truth_est`'s gyro
    pure (withDischarges n (loiterDischarges ++ Ardupilot.Harnesses.Chain.discharges none ++
      Ardupilot.Harnesses.Chain.supervised))

end Ardupilot.Harnesses.ApFull
