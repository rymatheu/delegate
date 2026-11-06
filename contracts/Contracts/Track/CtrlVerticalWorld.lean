import Contracts.Track.CtrlVerticalD
import Contracts.Track.Frame

/-!
# `Vehicle.tick` in stages, and the frames the vertical channel needs

`tick_split`: on a tick of Auto mode (`in_auto`), `Vehicle.tick` is `auto_run` of `preAuto`
(sample, view, estimates) of `postMot` (motors' output) of `preMot` (scheduler, periods, rate
controller), with the actuators `actOf (postMot …)`; `auto_run_eq`, `wp_run_split`: `wp_run` is
`finW` (heading, thrust vector) of `postD` (`D_update_controller` and its `set_throttle_out`) of
`navW` (the navigator). Each is checked by normalising both sides (`dsimp`) and `rfl`.

The frames: the rate controller leaves the motors' throttle and filter cutoff (`rate_thr`); the
motors' output changes the throttle filter only in `update_throttle_filter` (`filt_output`); the
heading and thrust-vector stage changes neither the motors nor the position controller.
-/

namespace Contracts.Track.CtrlV

open Vehicle

noncomputable section

/-! ## `Vehicle.tick` in named stages -/

/-- The world before the motors' output: the scheduler step, the gyro, the periods, the rate
controller (with its writes into the motors) and its target reset. -/
def preMot (w : World) (smp : Sample) : World :=
  let first_tick := w.ticks32 == 0
  let w := { w with ticks32 := w.ticks32 + 1, micros := w.micros + smp.dt_us, last_loop_time_s := (if first_tick then (1.0 : Float32) / (400.0 : Float32) else smp.dt_us.toFloat32 * (1.0e-6 : Float32)) }
  let w := { w with sample.gyro := smp.gyro }
  let t := w.last_loop_time_s
  let w := { w with ps := AC_PosControl_lib.AC_PosControl.set_dt_s w.ps t, «as» := AC_Attitude_lib.AC_AttitudeControl_Multi.set_dt_s w.as t, ms := AP_Motors_lib.AP_MotorsMatrix.set_dt_s w.ms t }
  let inp := attInputs w
  let ap := w.ap
  let w := withMotors w (fun o => AC_Attitude_lib.AC_AttitudeControl_Multi.rate_controller_run ap w.as o inp)
  { w with «as» := AC_Attitude_lib.AC_AttitudeControl_Multi.rate_controller_target_reset w.as }

/-- The world after the motors' output. -/
def postMot (w : World) : World :=
  let r := AP_Motors_lib.AP_MotorsMatrix.output w.mp w.ms #[] (motorsInputs w)
  { w with mp := r.1, ms := r.2.1 }

/-- The four actuators the tick returns. -/
def actOf (w : World) : Array Float32 :=
  #[w.ms._actuator[0]!, w.ms._actuator[1]!, w.ms._actuator[2]!, w.ms._actuator[3]!]

/-- The world before `ModeAuto::run`: the sample, the view, the estimates, the landed gain and
the reset method. -/
def preAuto (w : World) (smp : Sample) : World :=
  let w := { w with sample := { smp with gyro := w.sample.gyro } }
  let w := viewUpdate w
  let w := { w with ps := AC_PosControl_lib.AC_PosControl.update_estimates w.ps (posInputs w) false }
  let w := { w with «as» := AC_Attitude_lib.AC_AttitudeControl_Multi.landed_gain_reduction w.ap w.as false }
  { w with ps := AC_PosControl_lib.AC_PosControl.set_reset_handling_method w.ps .MoveVehicle }

theorem withMotors_in_auto (w : World) f : (withMotors w f).in_auto = w.in_auto := by
  unfold withMotors
  rcases f (attOutputs w.ms) with ⟨a, o⟩
  rfl

theorem tick_split (w : World) (smp : Sample) (hin : w.in_auto = true) :
    Vehicle.tick w smp = (auto_run (preAuto (postMot (preMot w smp)) smp), actOf (postMot (preMot w smp))) := by
  cases w
  simp only at hin
  subst hin
  unfold Vehicle.tick preMot postMot actOf preAuto
  dsimp only [Id.run, viewUpdate, withMotors_in_auto, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
  rfl


/-- `ModeAuto::run` when the mission has started. -/
theorem auto_run_eq (w : World) (hw : w.au.waiting_to_start = false) :
    auto_run w = wp_run (mission_update w) := by
  simp only [auto_run, hw, Bool.false_eq_true, ite_false]

/-- The world after the navigator's update in `wp_run` (spool state, `update_wpnav`, its calls
into the position controller). -/
def navW (w : World) : World :=
  let w := { w with ms := AP_Motors_lib.AP_MotorsMatrix.set_desired_spool_state w.ms .THROTTLE_UNLIMITED }
  let (wps, log, _) := AC_WPNav_lib.AC_WPNav.update_wpnav w.wpp w.wps #[] (wpInputs w)
  afterWP w w.wpp wps log

/-- The world after `D_update_controller` and its `set_throttle_out`. -/
def postD (w : World) : World :=
  let (pp, ps, evs) := AC_PosControl_lib.AC_PosControl.D_update_controller w.pp w.ps #[] (posInputs w)
  applyPos { w with pp, ps } evs

/-- The world after the heading and the thrust vector. -/
def finW (w : World) : World :=
  let tv := AC_PosControl_lib.AC_PosControl.get_thrust_vector w.ps
  let (w', heading) := auto_yaw_get_heading w
  { w' with «as» := AC_Attitude_lib.AC_AttitudeControl_Multi.input_thrust_vector_heading w'.ap w'.as (attInputs w') { x := tv.x, y := tv.y, z := tv.z } heading }

theorem wp_run_split (w : World) : wp_run w = finW (postD (navW w)) := by
  unfold wp_run finW postD navW
  dsimp only [Id.run]
  rfl

theorem finW_ms (w : World) : (finW w).ms = w.ms := by
  simp only [finW, auto_yaw_get_heading, auto_yaw_yaw_rad, auto_yaw_rate_rads]

theorem finW_ps (w : World) : (finW w).ps = w.ps := by
  simp only [finW, auto_yaw_get_heading, auto_yaw_yaw_rad, auto_yaw_rate_rads]


theorem applyPos_single (w : World) (t : Float32) (b : Bool) (c : Float32) :
    applyPos w (#[].push (AC_PosControl_lib.Output.set_throttle_out t b c)) =
      withMotors w (fun o => AC_Attitude_lib.AC_AttitudeControl_Multi.set_throttle_out w.ap w.as o
        (attInputs w) t b c) := by
  rfl

theorem withMotors_ps (w : World) f : (withMotors w f).ps = w.ps := by
  unfold withMotors; rcases f (attOutputs w.ms) with ⟨a, o⟩; rfl

theorem withMotors_ms (w : World) f : (withMotors w f).ms = applyAtt w.ms (f (attOutputs w.ms)).2 := by
  unfold withMotors; rcases f (attOutputs w.ms) with ⟨a, o⟩; rfl

theorem applyAtt_thr_in (ms : AP_Motors_lib.AP_MotorsMatrix.State) o :
    (applyAtt ms o)._throttle_in = o.set_throttle := rfl

theorem applyAtt_filt (ms : AP_Motors_lib.AP_MotorsMatrix.State) o :
    (applyAtt ms o)._throttle_filter.output = ms._throttle_filter.output := rfl

theorem applyAtt_cut (ms : AP_Motors_lib.AP_MotorsMatrix.State) o :
    (applyAtt ms o)._throttle_filter.cutoff_freq = o.set_throttle_filter_cutoff := rfl

end

set_option maxHeartbeats 4000000
set_option linter.unusedSimpArgs false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false
set_option linter.unnecessarySeqFocus false

section RateFrame
open AC_Attitude_lib AC_AttitudeControl_Multi

theorem rate_dt_thr (p : Params) (s : State) (o : Outputs) inp g dt :
    (rate_controller_run_dt p s o inp g dt).2.set_throttle = o.set_throttle ∧
      (rate_controller_run_dt p s o inp g dt).2.set_throttle_filter_cutoff = o.set_throttle_filter_cutoff := by
  frame_gen Outputs (fun o' : Outputs => o'.set_throttle = o.set_throttle ∧
      o'.set_throttle_filter_cutoff = o.set_throttle_filter_cutoff) (rate_controller_run_dt p s o inp g dt)
    using first | exact ⟨rfl, rfl⟩ | assumption


theorem rate_thr (p : Params) (s : State) (o : Outputs) inp :
    (rate_controller_run p s o inp).2.set_throttle = o.set_throttle ∧
      (rate_controller_run p s o inp).2.set_throttle_filter_cutoff = o.set_throttle_filter_cutoff := by
  simp only [rate_controller_run, Id.run]
  exact rate_dt_thr p s o inp _ _

end RateFrame

section MotFrame
open AP_Motors_lib AP_MotorsMatrix

theorem filt_check_for_failed_motor (s : State) inp x :
    (check_for_failed_motor s inp x)._throttle_filter = s._throttle_filter := by
  frame_gen State (fun st : State => st._throttle_filter = s._throttle_filter) (check_for_failed_motor s inp x)
    using first | rfl | assumption

theorem filt_output_armed_stabilizing (p : Params) (s : State) inp :
    (output_armed_stabilizing p s inp)._throttle_filter = s._throttle_filter := by
  frame_gen State (fun st : State => st._throttle_filter = s._throttle_filter) (output_armed_stabilizing p s inp)
    using first | rfl | assumption | (simp only [filt_check_for_failed_motor]; assumption)

theorem filt_output_logic (p : Params) (s : State) : (output_logic p s).2._throttle_filter = s._throttle_filter := by
  frame_gen State (fun st : State => st._throttle_filter = s._throttle_filter) (output_logic p s)
    using first | rfl | assumption

theorem filt_output_to_motors (p : Params) (s : State) o :
    (output_to_motors p s o).1._throttle_filter = s._throttle_filter := by
  frame_gen State (fun st : State => st._throttle_filter = s._throttle_filter) (output_to_motors p s o)
    using first | rfl | assumption

theorem filt_output (p : Params) (s : State) o inp :
    (output p s o inp).2.1._throttle_filter = (update_throttle_filter s inp)._throttle_filter := by
  simp only [output, Id.run]
  show (update_external_limits _)._throttle_filter = _
  rw [show ∀ x : State, (update_external_limits x)._throttle_filter = x._throttle_filter from
    fun x => rfl]
  rw [filt_output_to_motors, filt_output_armed_stabilizing, filt_output_logic]

end MotFrame

end Contracts.Track.CtrlV
