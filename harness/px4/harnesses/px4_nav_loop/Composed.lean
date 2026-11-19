import Harness.Compose
import px4.harnesses.px4_chain.Discharges
import px4.harnesses.px4_cmd_loop.Composed
import px4.modules.px4_navigator.Module
import px4.modules.px4_merge_ack.Module
import px4.modules.px4_drive_nav.Module

/-! # px4_nav_loop: px4_cmd_loop with PX4's navigator; the driver is only a ground station

[plant_sim, px4_drive_nav, px4_sim_in, px4_sensors, px4_rate, px4_alloc, px4_ekf2, px4_att,
px4_navigator, px4_fmm, px4_pos, px4_land, px4_commander, px4_merge_ack, px4_sim_out], by name,
no rename. The driver sends vehicle_command messages only (arm, NAV_TAKEOFF, DO_REPOSITION,
NAV_LAND); commander makes the modes, the arming state and home; navigator (with its dataman)
makes the position setpoint triplet from the commands and the modes: the takeoff setpoint, the
loiter at the reposition point, the landing. px4_land detects the landing and commander disarms
(COM_DISARM_LAND). commander and navigator both acknowledge commands on vehicle_command_ack
(`pub vehicle_command_ack by`); px4_merge_ack makes the one queue.

Order: navigator before the flight mode manager (which reads its triplet in the same tick) and
before commander (it reads commander's vehicle_status, home and the land detector of the previous
tick, as the driver does: so a command the driver paces on vehicle_status reaches navigator in a
step with a vehicle_status, px4_navigator's `command_paced`). -/

namespace Px4.Harnesses.Px4NavLoop

open Harness Harness.Contract.Lang
open Px4.Harnesses.Px4CmdLoop (paramClauses restrict)

/-- The parameters: px4_cmd_loop's, and navigator's PX4 defaults with the X500 airframe's. The
airframe's values replace the other modules' defaults of the same parameters (NAV_ACC_RAD is
also the flight mode manager's: both read the one parameter store on the vehicle). -/
def navParams : List Clause :=
  let sets := Px4.Modules.Px4Navigator.x500Sets.map (s!"default_{·.1}")
  (paramClauses.filter fun c => !sets.contains c.name) ++ Px4.Modules.Px4Navigator.x500Params

/-- The navigator's inputs nothing in the loop makes: no mission upload (no MAVLink), no
storage requests from outside, no fixed-wing controller status, no wind estimate. -/
def navQuiet : List String :=
  ["mission", "position_controller_status", "position_controller_landing_status", "wind"]

def script (s : String) : Clause :=
  ⟨s, "arm_s" =. 12 ∧. "takeoff_s" =. 13 ∧. "repos_s" =. 25 ∧. "repos_n" =. 10 ∧.
    "land_s" =. 38⟩

def mission (n : Node) (noise : Bool) : Regime where
  name := if noise then "x500_nav_noise" else "x500_nav"
  doc := "X500 with PX4's commander and navigator, commanded by a ground station: arm at 12 s, \
    takeoff at 13 s, reposition 10 m north at 25 s, land at 38 s" ++
    (if noise then ", sensor noise" else "")
  clauses := navParams ++ restrict n (
    Px4.Modules.Px4Commander.pinned Px4.Modules.Px4Commander.healthyTopics
      Px4.Modules.Px4Commander.healthyValues
      (["battery_status_voltage_v", "battery_status_remaining", "battery_status_current_a",
        "battery_status_current_average_a"]) ++
    (Px4.Modules.Px4Commander.groundFree.filter (·.name == "battery_charged")) ++
    Px4.Modules.Px4Commander.silent) ++ [
    ⟨"noise", "noise_on" =. (if noise then tt else ff)⟩, script "script"] ++
    restrict n ((["hover_thrust_estimate", "autotune_attitude_control_status",
      "failure_detector_status", "goto_setpoint", "velocity_limits", "failsafe_flags"] ++
        navQuiet).map fun t => ⟨s!"quiet_{t}", ¬. s!"{t}_updated"⟩) ++
    restrict n [⟨"no_storage_requests", "dataman_request_mirror_count" =. 0⟩,
      ⟨"no_mirror_mark", "dataman_request_mirror_by_px4_mavlink" =. ff⟩] ++
    -- and the mirror's 3400 words, unread when the count is 0, held at 0: drawn afresh at every
    -- step they made one 20000-step case's inputs file 652 MB (2026-11-18)
    [⟨"no_storage_words", (n.view.input.toList.filter fun f =>
        f.name.startsWith "dataman_request_mirror_" &&
          ((f.name.drop "dataman_request_mirror_".length).toString.all Char.isDigit)).foldl
        (fun e f => e ∧. Expr.var f.name =. 0) tt⟩]
  -- the timestamps of the topics the regime pins advance with the simulator's clock
  hints := (n.view.input.toList.filter fun f =>
    f.name.endsWith "_timestamp" || f.name.endsWith "_timestamp_sample").map
      fun f => Hint.increasing f.name 2500 2500 2500

/-! ### What the loop achieves against the simulator's truth -/

open Px4.Harnesses.Px4AutoLoop (tn te td)

private def window (a b : Float) : Expr :=
  (Expr.lit (a * 1e6).toFloat32.toBits) ≤. "t_us" ∧. Expr.var "t_us" <.
    (Expr.lit (b * 1e6).toFloat32.toBits)

private def tracks (bxy bz : Float) : Expr :=
  abs (tn - "trajectory_setpoint_position_0") ≤. Expr.lit bxy.toFloat32.toBits ∧.
  abs (te - "trajectory_setpoint_position_1") ≤. Expr.lit bxy.toFloat32.toBits ∧.
  abs (td - "trajectory_setpoint_position_2") ≤. Expr.lit bz.toFloat32.toBits

private def ekfAltitude (bound : Float) : Expr :=
  ¬. "vehicle_local_position_z_valid" ∨. ¬. "vehicle_local_position_z_global" ∨.
    abs ("vehicle_local_position_z" - td) ≤. Expr.lit bound.toFloat32.toBits

/-- The first statement of the truth clauses of this loop. Two were refuted by the first flight
(`harness run px4_nav_loop --steps 20000 --seed 1 --regime x500_nav_noise`):
* `ekf2_altitude_vs_truth` (px4_auto_loop's bound, 0.8 m, over the whole run): 308 violations
  from step 17786 (44.47 s), largest error 0.818 m, after the touchdown. Mechanism, from a replay
  with the simulator's IMU (noise seed 1, py/regime_case.py): at touchdown (41.44 s, 0.68 m/s
  down) the simulator's ground contact holds the position while its accelerometer reports, for
  about 0.4 s, specific forces of -3.5 to -6 m/s^2 against gravity's 9.8 (41.72-41.92 s): EKF2
  integrates a downward velocity of 0.4-0.5 m/s that the vehicle does not have and corrects it
  only slowly from the barometer (EKF2_BARO_NOISE 3.5 m), so its height runs below the truth at
  about 0.4 m/s until the land detector reports landed (45 s), then recovers. The 0.8 m bound is
  the flight's mechanism (the baro calibration step); the landing is another one.
* `landed_at_reposition` with `-0.2 ≤ pos_d` (on the ground at the start's height): at 48 s
  pos_d = -0.487: the gorge's floor 9.8 m north is 0.355 m above the start's (the vehicle stood
  still there, landed and disarmed). -/
def truthClausesAsFirstStated : List Clause := [
  ⟨"ekf2_altitude_vs_truth", ekfAltitude 0.8⟩,
  ⟨"landed_at_reposition", ¬. window 48 1000 ∨.
    (abs ("pos_n" - (10 : Expr)) ≤. 1.5 ∧. abs "pos_e" ≤. 1.5 ∧. -0.2 ≤. "pos_d" ∧.
     "vehicle_land_detected_landed" ∧. "vehicle_status_arming_state" =. 1)⟩]

/-- Against the simulator's truth (EKF2's frame as in px4_auto_loop):
* EKF2's height within 0.8 m until the land command (38 s; px4_auto_loop's mechanism), within
  1.5 m after it: the landing's mechanism above, an integrated 0.4-0.8 m/s of false descent
  corrected over 1-2 s (0.82 m seen); EKF2's horizontal position within 1 m throughout.
* the holds (21-25 s after the takeoff, 34-38 s after the reposition): the truth within 0.5 m of
  the flight mode manager's setpoint horizontally, 0.8 m vertically (EKF2's errors and a few cm
  of tracking).
* `landed_at_reposition`, from 48 s: landed, disarmed, still (|vel_d| ≤ 0.05 m/s), within 1.5 m
  of 10 m north of the simulator's start: the binary32 target (0.21 m north, 0.33 m east at
  most), EKF2's horizontal error at home and at the landing (0.5 m each), a drift of 0.2 m in the
  descent. -/
def truthClauses : List Clause :=
  (Px4.Harnesses.Px4AutoLoop.truthClauses.filter (·.name == "ekf2_horizontal_vs_truth")) ++ [
  ⟨"ekf2_altitude_vs_truth_in_flight", ¬. window 0 38 ∨. ekfAltitude 0.8⟩,
  ⟨"ekf2_altitude_vs_truth_landing", ¬. window 38 1000 ∨. ekfAltitude 1.5⟩,
  ⟨"takeoff_hold_tracks_setpoint", ¬. window 21 25 ∨. tracks 0.5 0.8⟩,
  ⟨"reposition_hold_tracks_setpoint", ¬. window 34 38 ∨. tracks 0.5 0.8⟩,
  ⟨"landed_at_reposition", ¬. window 48 1000 ∨.
    (abs ("pos_n" - (10 : Expr)) ≤. 1.5 ∧. abs "pos_e" ≤. 1.5 ∧. abs "vel_d" ≤. 0.05 ∧.
     "vehicle_land_detected_landed" ∧. "vehicle_status_arming_state" =. 1)⟩]

def withTruth (n : Node) : Node :=
  match n with
  | .system s => .system { s with contract := { s.contract with
      guarantee := s.contract.guarantee ++ truthClauses } }
  | m => m

def system (_ : Unit := ()) : Except String Node := do
  let n ← composeAll "px4_nav_loop"
    [.module Sim.Modules.PlantSim.module, .module Px4.Modules.Px4DriveNav.module,
     .module Px4.Modules.Px4CmdWindow.module,
     .module Px4.Modules.Px4SimIn.module, .module Px4.Modules.Px4Sensors.module,
     .module Px4.Modules.Px4Rate.module, .module Px4.Modules.Px4Alloc.module,
     .module Px4.Modules.Px4Ekf2.module, .module Px4.Modules.Px4Att.module,
     .module Px4.Modules.Px4Navigator.module, .module Px4.Modules.Px4Fmm.module,
     .module Px4.Modules.Px4Pos.module, .module Px4.Modules.Px4Land.module,
     .module Px4.Modules.Px4Commander.module, .module Px4.Modules.Px4MergeAck.module,
     ← Px4.Harnesses.Px4ClosedRate.simOut]
  let n := withDischarges n Px4.Harnesses.Chain.window
  let n := Px4.Harnesses.Chain.withGlue n
  return Px4.Harnesses.Px4ClosedRate.withImuDefaults
    (withTruth (withRegime (withRegime n (mission n false)) (mission n true)))

end Px4.Harnesses.Px4NavLoop
