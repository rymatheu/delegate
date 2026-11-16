import Contracts.Track.Induction.TickGlue
import Contracts.Track.CtrlVertical

/-!
# The glue of hover, part (1): `Vehicle.tick` as the explicit sequence of its calls

REACH.md §"Glue" (1). `tick_split` writes one `Vehicle.tick` as its calls, in the order of
`copter_ref.cpp`, each applied to the world the previous one hands on:

| stage | call (Vehicle.lean) |
|---|---|
| `schedW` | `AP_Scheduler::loop`: `ticks32 + 1`, `micros + dt_us`, `last_loop_time_s` (first tick: `1.0f/400.0f`) |
| `gyroW` | `AP_InertialSensor::update`: the tick's gyro |
| `dtW` | `set_dt_s` × 3 (position controller, attitude controller, motors) |
| `rateW` | `rate_controller_run` (writes the motors' roll/pitch/yaw/throttle inputs) |
| `tresetW` | `rate_controller_target_reset` |
| `CtrlV.postMot` | `AP_MotorsMulticopter::output`; the four actuators are read here (`CtrlV.actOf`) |
| `smpW` | `read_AHRS`: the sample (gyro kept) |
| `viewUpdate` | the AHRS view |
| `estW` | `update_estimates` |
| `modeW` | first tick only (`in_auto = false`): `ModeAuto::init` and the rate time constants (`TG.initW`) |
| `landW` | `landed_gain_reduction` |
| `rhmW` | `set_reset_handling_method` |
| `missionW` | `ModeAuto::run`: `mission_start` (first run) or `mission_update` |
| `CtrlV.navW` | `wp_run`: spool state, `update_wpnav`, its events replayed (`replayPos`) |
| `dW`, `applyPos` | `D_update_controller`, then its events (`set_throttle_out`) |
| `CtrlV.finW` | `get_thrust_vector`, `auto_yaw` heading, `input_thrust_vector_heading` |

The hold (`tick_hold`): Auto mode, the mission past its start and not running
(`au.state ≠ RUNNING`, i.e. `COMPLETE` after the single waypoint): `missionW` is the identity.
With the navigator steady (`SpeedSteady`, no terrain), the tick hands the position controller,
in order, `set_pos_terrain_target_D_m 0`, `set_pos_vel_accel_NED_m P V A`, **one**
`NE_update_controller`, then `D_update_controller` (`tick_hold_ps`). `offZ_tick_hold`: the horizontal
offsets stay zero from tick to tick (`OffZero` preserved).

Proof method: each equation is checked by unfolding both sides and `rfl`/`dsimp`, from the
coarser splits already proved (`CtrlV.tick_split`, `TG.tick_split_first`, `CtrlV.wp_run_split`,
`TG.navW_steady`).
-/

namespace Contracts.Track.Reach.Glue

open Vehicle Contracts.Track.CtrlV Contracts.Track.Induction.TG

noncomputable section

/-! ## The stages -/

/-- `AP_Scheduler::loop`: the tick counter, the clock, the loop time. -/
def schedW (w : World) (smp : Sample) : World :=
  { w with ticks32 := w.ticks32 + 1, micros := w.micros + smp.dt_us,
           last_loop_time_s := if w.ticks32 == 0 then (1.0 : Float32) / (400.0 : Float32)
             else smp.dt_us.toFloat32 * (1.0e-6 : Float32) }

/-- `AP_InertialSensor::update`: the tick's gyro. -/
def gyroW (w : World) (smp : Sample) : World := { w with sample.gyro := smp.gyro }

/-- `run_rate_controller_main`: `set_dt_s` of the position controller, the attitude controller and
the motors, with the loop time. -/
def dtW (w : World) : World :=
  { w with ps := AC_PosControl_lib.AC_PosControl.set_dt_s w.ps w.last_loop_time_s,
           «as» := AC_Attitude_lib.AC_AttitudeControl_Multi.set_dt_s w.as w.last_loop_time_s,
           ms := AP_Motors_lib.AP_MotorsMatrix.set_dt_s w.ms w.last_loop_time_s }

/-- `rate_controller_run`, writing the motors' inputs. -/
def rateW (w : World) : World :=
  withMotors w (fun o => AC_Attitude_lib.AC_AttitudeControl_Multi.rate_controller_run w.ap w.as o
    (attInputs w))

/-- `rate_controller_target_reset`. -/
def tresetW (w : World) : World :=
  { w with «as» := AC_Attitude_lib.AC_AttitudeControl_Multi.rate_controller_target_reset w.as }

/-- `read_AHRS`: the sample, with the gyro of the tick kept. -/
def smpW (w : World) (smp : Sample) : World := { w with sample := { smp with gyro := w.sample.gyro } }

/-- `read_inertia`: `update_estimates`. -/
def estW (w : World) : World :=
  { w with ps := AC_PosControl_lib.AC_PosControl.update_estimates w.ps (posInputs w) false }

/-- `set_mode(AUTO)` on the first tick (`ModeAuto::init`, the rate time constants). -/
def modeW (w : World) : World := if w.in_auto then w else initW w

/-- `landed_gain_reduction(false)`. -/
def landW (w : World) : World :=
  { w with «as» := AC_Attitude_lib.AC_AttitudeControl_Multi.landed_gain_reduction w.ap w.as false }

/-- `set_reset_handling_method(MoveVehicle)`. -/
def rhmW (w : World) : World :=
  { w with ps := AC_PosControl_lib.AC_PosControl.set_reset_handling_method w.ps .MoveVehicle }

/-- `ModeAuto::run` before `wp_run`: the mission's start (first run) or update. -/
def missionW (w : World) : World :=
  if w.au.waiting_to_start then { mission_start w with au.waiting_to_start := false }
  else mission_update w

/-- `D_update_controller` on the world: the new position controller and its events. -/
def dW (w : World) : World × AC_PosControl_lib.Outputs :=
  let r := AC_PosControl_lib.AC_PosControl.D_update_controller w.pp w.ps #[] (posInputs w)
  ({ w with pp := r.1, ps := r.2.1 }, r.2.2)

/-- The world before the motors' output. -/
def preMotS (w : World) (smp : Sample) : World := tresetW (rateW (dtW (gyroW (schedW w smp) smp)))

/-- The world `ModeAuto::run` receives. -/
def preNav (w : World) (smp : Sample) : World :=
  rhmW (landW (modeW (estW (viewUpdate (smpW (postMot (preMotS w smp)) smp)))))

/-! ## Unbounded time: the `ticks32` wrap -/

set_option maxRecDepth 100000 in
/-- `1.0f/400.0f` and `2500 · 1e-6f` are the same `float` (kernel evaluation of core's float
model). -/
theorem dt_first_eq : (1.0 : Float32) / (400.0 : Float32) =
    (2500 : UInt64).toFloat32 * (1.0e-6 : Float32) := by
  decide +kernel

/-- **The `ticks32` wrap is harmless for the loop time**: with the plant's period (`dt_us = 2500`)
the scheduler's loop time is `0.0025f` whether or not the tick counter reads `0` (the first tick,
or again after `2³²` ticks, REACH.md §5.3). Nothing else of `Vehicle.tick` reads `first_tick`. -/
theorem schedW_loop_time (w : World) (smp : Sample) (h : smp.dt_us = 2500) :
    (schedW w smp).last_loop_time_s = (1.0 : Float32) / (400.0 : Float32) := by
  simp only [schedW, h]
  split <;> [rfl; exact dt_first_eq.symm]

/-! ## The coarse splits are the explicit sequence -/

theorem preMot_eq (w : World) (smp : Sample) : preMot w smp = preMotS w smp := rfl

theorem postD_eq (w : World) : postD w = applyPos (dW w).1 (dW w).2 := rfl

theorem auto_run_missionW (w : World) : auto_run w = wp_run (missionW w) := by
  unfold auto_run missionW
  cases w.au.waiting_to_start <;> rfl

theorem withMotors_in_auto' (w : World) f : (withMotors w f).in_auto = w.in_auto :=
  withMotors_in_auto w f

theorem withMotors_au (w : World) f : (withMotors w f).au = w.au := by
  unfold withMotors
  rcases f (attOutputs w.ms) with ⟨a, o⟩
  rfl

/-- The stages before `ModeAuto::init` do not touch `in_auto`. -/
theorem pre_in_auto (w : World) (smp : Sample) :
    (estW (viewUpdate (smpW (postMot (preMotS w smp)) smp))).in_auto = w.in_auto := by
  simp only [estW, viewUpdate, smpW, postMot, preMotS, tresetW, rateW, withMotors_in_auto', dtW,
    gyroW, schedW]

/-- The world `ModeAuto::init` would receive. -/
def preMode (w : World) (smp : Sample) : World := estW (viewUpdate (smpW (postMot (preMotS w smp)) smp))

theorem preNav_def (w : World) (smp : Sample) : preNav w smp = rhmW (landW (modeW (preMode w smp))) := rfl

/-- After the first tick `ModeAuto::init` is skipped. -/
theorem modeW_auto (w : World) (smp : Sample) (hin : w.in_auto = true) :
    modeW (preMode w smp) = preMode w smp := by
  have h := pre_in_auto w smp
  rw [hin] at h
  unfold modeW
  rw [show (preMode w smp).in_auto = true from h]
  rfl

/-- On the first tick `ModeAuto::init` runs. -/
theorem modeW_first (w : World) (smp : Sample) (hin : w.in_auto = false) :
    modeW (preMode w smp) = initW (preMode w smp) := by
  have h := pre_in_auto w smp
  rw [hin] at h
  unfold modeW
  rw [show (preMode w smp).in_auto = false from h]
  rfl

/-- The stages before `ModeAuto::run` do not touch the mission state machine, after the first
tick. -/
theorem preNav_au (w : World) (smp : Sample) (hin : w.in_auto = true) : (preNav w smp).au = w.au := by
  rw [preNav_def, modeW_auto w smp hin]
  simp only [preMode, rhmW, landW, estW, viewUpdate, smpW, postMot, preMotS, tresetW, rateW,
    withMotors_au, dtW, gyroW, schedW]

/-- **`tick_split`: one tick is the explicit sequence of its calls.** -/
theorem tick_split (w : World) (smp : Sample) :
    Vehicle.tick w smp = (finW (postD (navW (missionW (preNav w smp)))),
      actOf (postMot (preMotS w smp))) := by
  cases hin : w.in_auto
  · rw [tick_split_first w smp hin, auto_run_missionW, wp_run_split, preNav_def,
      modeW_first w smp hin]
    rfl
  · rw [CtrlV.tick_split w smp hin, auto_run_missionW, wp_run_split, preNav_def,
      modeW_auto w smp hin]
    rfl

/-- After the first tick, `preNav` is `CtrlV.preAuto` of the motors' output. -/
theorem preNav_eq (w : World) (smp : Sample) (hin : w.in_auto = true) :
    preNav w smp = preAuto (postMot (preMot w smp)) smp := by
  rw [preNav_def, modeW_auto w smp hin]
  rfl

/-! ## The hold -/

/-- `mission_update` is the identity once the mission is not running (`COMPLETE`). -/
theorem mission_update_idle (w : World) (h : w.au.state ≠ .RUNNING) : mission_update w = w := by
  unfold mission_update
  have : (w.au.state != Vehicle.MissionState.RUNNING) = true := by simpa using h
  simp [Id.run, this]

/-- **The hold tick**: after the first tick, the mission past its start and not running. -/
theorem tick_hold (w : World) (smp : Sample) (hin : w.in_auto = true)
    (hws : w.au.waiting_to_start = false) (hst : w.au.state ≠ .RUNNING) :
    Vehicle.tick w smp = (finW (postD (navW (preNav w smp))), actOf (postMot (preMotS w smp))) := by
  rw [tick_split]
  have hau := preNav_au w smp hin
  have h1 : (preNav w smp).au.waiting_to_start = false := by rw [hau]; exact hws
  have h2 : (preNav w smp).au.state ≠ .RUNNING := by rw [hau]; exact hst
  simp only [missionW, h1, Bool.false_eq_true, ite_false, mission_update_idle _ h2]

/-- **The state handed to the position controller on a steady hold tick**: the navigator's two
setters, one `NE_update_controller`, then `D_update_controller`; nothing else of the tick writes
`ps` after it. -/
theorem tick_hold_ps (w : World) (smp : Sample) (hin : w.in_auto = true)
    (hws : w.au.waiting_to_start = false) (hst : w.au.state ≠ .RUNNING)
    (hS : SpeedSteady (preNav w smp).wpp (preNav w smp).wps)
    (hT : (preNav w smp).wps._is_terrain_alt = false) :
    ∃ P V A, navW (preNav w smp) = { spoolW (preNav w smp) with
        wps := { advW (preNav w smp) with
          _wp_last_update_ms := (wpInputs (spoolW (preNav w smp))).millis },
        ps := AC_PosControl_lib.AC_PosControl.NE_update_controller (preNav w smp).pp
          (AC_PosControl_lib.AC_PosControl.set_pos_vel_accel_NED_m
            (AC_PosControl_lib.AC_PosControl.set_pos_terrain_target_D_m (preNav w smp).ps 0.0)
            (p3 P) (f3 V) (f3 A))
          (posInputs (spoolW (preNav w smp))) } ∧
      (Vehicle.tick w smp).1.ps =
        (AC_PosControl_lib.AC_PosControl.D_update_controller (navW (preNav w smp)).pp
          (navW (preNav w smp)).ps #[] (posInputs (navW (preNav w smp)))).2.1 := by
  obtain ⟨P, V, A, hN⟩ := navW_steady (preNav w smp) hS hT
  refine ⟨P, V, A, hN, ?_⟩
  rw [tick_hold w smp hin hws hst]
  simp only [finW_ps, postD_ps]

/-! ## `OffZero` from tick to tick -/

open AC_PosControl_lib AC_PosControl in
/-- The position controller's state `preNav` hands on: `set_reset_handling_method` of
`update_estimates` of `set_dt_s` of the tick's start (after the first tick). -/
theorem preNav_ps (w : World) (smp : Sample) (hin : w.in_auto = true) :
    (preNav w smp).ps = set_reset_handling_method
      (update_estimates (set_dt_s w.ps (schedW w smp).last_loop_time_s)
        (posInputs (viewUpdate (smpW (postMot (preMotS w smp)) smp))) false) .MoveVehicle := by
  rw [preNav_def, modeW_auto w smp hin]
  simp only [preMode, rhmW, landW, estW]
  congr 2

open AC_PosControl_lib AC_PosControl in
/-- **`OffZero` is kept by a steady hold tick**: the horizontal offsets and their targets are zero
after the tick when they were before, given the conditions of `NE_update_controller`'s offset
lemma at the state the tick hands it (no EKF reset, the controller active, a finite period
`|dt| ≤ 1`, a finite jerk/acceleration ratio). -/
theorem offZ_tick_hold (hL : Contracts.Mission.LibmSpec) (w : World) (smp : Sample)
    (hin : w.in_auto = true) (hws : w.au.waiting_to_start = false) (hst : w.au.state ≠ .RUNNING)
    (hS : SpeedSteady (preNav w smp).wpp (preNav w smp).wps)
    (hT : (preNav w smp).wps._is_terrain_alt = false) (hO : Contracts.Track.Induction.TG.OffZ w.ps)
    (hekf : (posInputs (spoolW (preNav w smp))).get_position_NE_reset_count =
      (preNav w smp).ps._ahrs_position_NE_reset_count)
    (hact : NE_is_active (preNav w smp).ps (posInputs (spoolW (preNav w smp))) = true)
    (hdt : (preNav w smp).ps._dt_s.IsFinite) (hdt1 : |(preNav w smp).ps._dt_s.toReal| ≤ 1)
    (hk : ((preNav w smp).ps._jerk_max_ne_msss / (preNav w smp).ps._accel_max_ne_mss).IsFinite) :
    Contracts.Track.Induction.TG.OffZ (Vehicle.tick w smp).1.ps := by
  obtain ⟨P, V, A, hN, hps⟩ := tick_hold_ps w smp hin hws hst hS hT
  rw [hps]
  have e : (navW (preNav w smp)).ps =
      NE_update_controller (preNav w smp).pp
        (set_pos_vel_accel_NED_m (set_pos_terrain_target_D_m (preNav w smp).ps 0.0) (p3 P) (f3 V) (f3 A))
        (posInputs (spoolW (preNav w smp))) := by
    rw [hN]
  have h0 : Contracts.Track.Induction.TG.OffZ (preNav w smp).ps := by
    rw [preNav_ps w smp hin]
    exact offZ_set_reset_handling_method (offZ_update_estimates (offZ_set_dt_s hO _) _ _) _
  rw [e]
  apply offZ_D_update
  clear e hps hN
  generalize (preNav w smp).pp = pp at *
  generalize posInputs (spoolW (preNav w smp)) = inp at *
  generalize (preNav w smp).ps = s0 at *
  have h1 := offZ_set_pos_vel_accel_NED_m (offZ_set_pos_terrain_target_D_m h0 0.0) (p3 P) (f3 V) (f3 A)
  exact offZ_NE_update hL pp _ inp h1 hekf hact hdt hdt1 hk

end

end Contracts.Track.Reach.Glue
