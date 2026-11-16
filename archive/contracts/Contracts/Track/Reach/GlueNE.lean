import Contracts.Track.Reach.GlueTick

/-!
# The glue of hover, part (2): `NEGlue` on a hold tick

INDUCTION.md's `NEGlue w₀ x t` (Horiz.lean) is what M6's `HCtl.horizontal_tick_eq_D` needs from one
tick: the call of `NE_update_controller` with its region `HCtl.NERegion`, the active
`D_update_controller` after it, and the readouts (`posTarget`, the sample, `velTarget`, the PID
states of `habs`, `accDes` before; the PID states of `habs` and the command `cmd` after).

`neGlue_hold`: on a steady hold tick (`GlueTick.tick_hold_ps`), with the state the tick hands to
`NE_update_controller` (`set_pos_vel_accel_NED_m P V A` of `set_pos_terrain_target_D_m 0` of the
estimates of the tick) in `NERegion` and the vertical controller active after it, `NEGlue w₀ x t`
holds. The readouts are matched by frames:

* the targets after the tick are those the navigator handed: `D_update_controller` leaves the
  horizontal `_pos_desired`, `_vel_desired`, `_accel_desired` alone (`nef_D`), and
  `NE_update_controller` keeps `_vel_desired`, `_accel_desired` and, in its region, the value of
  `_pos_desired` (`ne_posd_val`: the P controller returns the target unchanged and the offsets are
  zero, so `(d + 0) − 0 = d` in `double`);
* the estimates are the sample (`HCtl.estimates_ne_world`), the PID state is the one before the
  tick (`set_dt_s`, `update_estimates`, the setters leave `_pid_vel_ne_m` alone);
* after the tick, the world is the D update of the NE update (`tick_hold_ps`), and the command is
  the horizontal part of the thrust vector (`HCtl.thrust_xy`).
-/

namespace Contracts.Track.Reach.Glue

open Vehicle Contracts.Track.CtrlV Contracts.Track.Induction.TG Contracts.Mission
open AC_PosControl_lib AC_PosControl Contracts.Track.HCtl Float.Model UnpackedFloat

noncomputable section

/-! ## Frames of the position controller's calls -/

section Frames

variable (s : State) (inp : Inputs)

theorem cy_posd : (calculate_yaw_and_rate_yaw s inp)._pos_desired_ned_m = s._pos_desired_ned_m := by
  unfold calculate_yaw_and_rate_yaw; simp only [Id.run]; split_ifs <;> rfl
theorem cy_veld : (calculate_yaw_and_rate_yaw s inp)._vel_desired_ned_ms = s._vel_desired_ned_ms := by
  unfold calculate_yaw_and_rate_yaw; simp only [Id.run]; split_ifs <;> rfl
theorem cy_accd :
    (calculate_yaw_and_rate_yaw s inp)._accel_desired_ned_mss = s._accel_desired_ned_mss := by
  unfold calculate_yaw_and_rate_yaw; simp only [Id.run]; split_ifs <;> rfl

end Frames

/-- The horizontal targets a call leaves alone. -/
def NEF (s t : State) : Prop :=
  t._pos_desired_ned_m.x = s._pos_desired_ned_m.x ∧ t._pos_desired_ned_m.y = s._pos_desired_ned_m.y ∧
  t._vel_desired_ned_ms.x = s._vel_desired_ned_ms.x ∧ t._vel_desired_ned_ms.y = s._vel_desired_ned_ms.y ∧
  t._accel_desired_ned_mss.x = s._accel_desired_ned_mss.x ∧
  t._accel_desired_ned_mss.y = s._accel_desired_ned_mss.y

theorem nef_refl (s : State) : NEF s s := ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

set_option maxHeartbeats 4000000 in
/-- `D_update_controller` leaves the horizontal targets alone. -/
theorem nef_D (p : Params) (s : State) (o : Outputs) (inp : Inputs) :
    NEF s (D_update_controller p s o inp).2.1 := by
  frame_gen State (fun t : State => NEF s t) (D_update_controller p s o inp)
    using first | exact nef_refl s | assumption

set_option maxHeartbeats 4000000 in
/-- `update_estimates` leaves the NE velocity PID alone. -/
theorem pidne_UE (s : State) (inp : Inputs) (hv : Bool) :
    (update_estimates s inp hv)._pid_vel_ne_m = s._pid_vel_ne_m := by
  frame_gen State (fun t : State => t._pid_vel_ne_m = s._pid_vel_ne_m) (update_estimates s inp hv)
    using first | rfl | assumption

section NE

variable (p : Params) (s : State) (inp : Inputs)
  (h : inp.get_position_NE_reset_count = s._ahrs_position_NE_reset_count)
  (ha : NE_is_active s inp = true)
include h ha

/-- `NE_update_controller` (no EKF reset, active) keeps `_vel_desired`, `_accel_desired`, and writes
`_pos_desired` as the P controller's target minus the offset. -/
theorem ne_desired :
    (NE_update_controller p s inp)._vel_desired_ned_ms = (nS3 s inp)._vel_desired_ned_ms ∧
    (NE_update_controller p s inp)._accel_desired_ned_mss = (nS3 s inp)._accel_desired_ned_mss ∧
    (NE_update_controller p s inp)._pos_desired_ned_m.x =
      (Vector2p.op_sub_Vector2p ({ x := (nP p (nS3 s inp)).2.1.x, y := (nP p (nS3 s inp)).2.1.y } :
        Vector2p.State) (Vector3p.xy (nS3 s inp)._pos_offset_ned_m)).x ∧
    (NE_update_controller p s inp)._pos_desired_ned_m.y =
      (Vector2p.op_sub_Vector2p ({ x := (nP p (nS3 s inp)).2.1.x, y := (nP p (nS3 s inp)).2.1.y } :
        Vector2p.State) (Vector3p.xy (nS3 s inp)._pos_offset_ned_m)).y := by
  unfold NE_update_controller
  simp only [Id.run, ekf_noop s inp h, ha, Bool.not_true, Bool.false_eq_true, ite_false, cy_posd,
    cy_veld, cy_accd]
  split <;> split <;> exact ⟨rfl, rfl, rfl, rfl⟩

end NE

/-- `double` subtraction of a zero is exact. -/
theorem F64.sub_zero_val {a z : Float} (ha : a.IsFinite) (hz : z.IsFinite) (h0 : z.toReal = 0) :
    (a - z).IsFinite ∧ (a - z).toReal = a.toReal := by
  have hm : |a.toReal - z.toReal| ≤ maxFinite := by
    rw [h0, sub_zero]; exact Float.abs_toReal_le_maxFinite a
  obtain ⟨b1, b2⟩ := Float.sub_bracket ha hz hm ha
  exact ⟨(Float.sub_err_all ha hz hm).1, le_antisymm (b2 (by rw [h0, sub_zero]))
    (b1 (by rw [h0, sub_zero]))⟩

/-- **In its region, `NE_update_controller` keeps the value of the position target**: the P
controller returns the target `d + o` unchanged (`p_spec`, linear zone), and `(d + o) − o = d` with
the offset `o = 0` (`NERegion.off`). -/
theorem ne_posd_val (hL : LibmSpec) (p : Params) (s : State) (inp : Inputs) (R : NERegion p s inp) :
    (NE_update_controller p s inp)._pos_desired_ned_m.x.toReal = s._pos_desired_ned_m.x.toReal ∧
    (NE_update_controller p s inp)._pos_desired_ned_m.y.toReal = s._pos_desired_ned_m.y.toReal := by
  obtain ⟨-, -, ex, ey⟩ := ne_desired p s inp R.ekf R.active
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, -⟩ := nS3_eq s inp
  have off := R.off
  set s3 := nS3 s inp with hs3
  obtain ⟨ftx, etx, -, -⟩ := pos_vals hL (q3 ▸ R.spx) off.px.1 off.px.2 (q8 ▸ R.dpx.1)
    (by rw [q8]; exact R.dpx.2)
  obtain ⟨fty, ety, -, -⟩ := pos_vals hL (q3 ▸ R.spy) off.py.1 off.py.2 (q8 ▸ R.dpy.1)
    (by rw [q8]; exact R.dpy.2)
  obtain ⟨-, -, fmx, emx⟩ := pos_vals hL (q4 ▸ R.px) off.px.1 off.px.2 (q8 ▸ R.dpx.1)
    (by rw [q8]; exact R.dpx.2)
  obtain ⟨-, -, fmy, emy⟩ := pos_vals hL (q4 ▸ R.py) off.py.1 off.py.2 (q8 ▸ R.dpy.1)
    (by rw [q8]; exact R.dpy.2)
  rw [← nPosTgt_x] at ftx etx
  rw [← nPosTgt_y] at fty ety
  rw [← nCombPos_x] at fmx emx
  rw [← nCombPos_y] at fmy emy
  rw [q3] at etx ety
  rw [q4] at emx emy
  have hPR : PosRegion ({ x := (nPosTgt s3).x, y := (nPosTgt s3).y } : Vector2p.State)
      (nCombPos s3) := ⟨ftx, fty, fmx, fmy, by simp only [etx, ety, emx, emy]; exact R.e⟩
  have hPg : PosGains p._p_pos_ne_m s3._p_pos_ne_m := q1 ▸ R.posg
  obtain ⟨hT, -, -, -⟩ := p_spec hL p._p_pos_ne_m s3._p_pos_ne_m _ _ hPg hPR
  change (nP p s3).2.1 = _ at hT
  rw [ex, ey, hT]
  refine ⟨?_, ?_⟩
  · exact (F64.sub_zero_val ftx off.px.1 off.px.2).2.trans etx
  · exact (F64.sub_zero_val fty off.py.1 off.py.2).2.trans ety

/-! ## The readouts of a hold tick -/

/-- The state a steady hold tick hands to `NE_update_controller`. -/
def neIn (w : World) (smp : Sample) (P : AC_WPNav_lib.Vector3p.State)
    (V A : AC_WPNav_lib.Vector3f.State) : State :=
  set_pos_vel_accel_NED_m (set_pos_terrain_target_D_m (preNav w smp).ps 0.0) (p3 P) (f3 V) (f3 A)

/-- What `preNav` hands on keeps the NE PID of the tick's start, and its estimates are the sample. -/
theorem preNav_pid_est (w : World) (smp : Sample) (hin : w.in_auto = true) :
    (preNav w smp).ps._pid_vel_ne_m = w.ps._pid_vel_ne_m ∧
    (preNav w smp).ps._pos_estimate_ned_m.x = smp.pos.x ∧
    (preNav w smp).ps._pos_estimate_ned_m.y = smp.pos.y ∧
    (preNav w smp).ps._vel_estimate_ned_ms.x = smp.vel.x ∧
    (preNav w smp).ps._vel_estimate_ned_ms.y = smp.vel.y := by
  rw [preNav_ps w smp hin]
  obtain ⟨e1, e2, e3, e4⟩ := estimates_ne_world (viewUpdate (smpW (postMot (preMotS w smp)) smp))
    (set_dt_s w.ps (schedW w smp).last_loop_time_s)
  exact ⟨pidne_UE _ _ _, e1, e2, e3, e4⟩

set_option maxHeartbeats 1000000 in
/-- **`NEGlue` on a steady hold tick**: after the first tick, with the mission past its start and
not running, the navigator steady and no terrain, the tick hands `NE_update_controller` the state
`neIn … P V A` (`tick_hold_ps`); if that call is in `NERegion` and the vertical controller is active
after it, then `NEGlue w₀ x t` (INDUCTION.md's `ne_glue` at tick `t`) holds. -/
theorem neGlue_hold (hL : LibmSpec) {w₀ : World} {x : ℕ → Mission.X} (hx : x ∈ Mctrl w₀) (t : ℕ)
    (hin : (Induction.run w₀ x t).in_auto = true)
    (hws : (Induction.run w₀ x t).au.waiting_to_start = false)
    (hst : (Induction.run w₀ x t).au.state ≠ .RUNNING)
    (hS : SpeedSteady (preNav (Induction.run w₀ x t) (x t).smp).wpp
      (preNav (Induction.run w₀ x t) (x t).smp).wps)
    (hT : (preNav (Induction.run w₀ x t) (x t).smp).wps._is_terrain_alt = false) :
    ∃ P V A,
      (navW (preNav (Induction.run w₀ x t) (x t).smp)).ps =
        NE_update_controller (preNav (Induction.run w₀ x t) (x t).smp).pp
          (neIn (Induction.run w₀ x t) (x t).smp P V A)
          (posInputs (spoolW (preNav (Induction.run w₀ x t) (x t).smp))) ∧
      (NERegion (preNav (Induction.run w₀ x t) (x t).smp).pp
          (neIn (Induction.run w₀ x t) (x t).smp P V A)
          (posInputs (spoolW (preNav (Induction.run w₀ x t) (x t).smp))) →
        D_is_active (D_handle_ekf_reset (NE_update_controller
            (preNav (Induction.run w₀ x t) (x t).smp).pp
            (neIn (Induction.run w₀ x t) (x t).smp P V A)
            (posInputs (spoolW (preNav (Induction.run w₀ x t) (x t).smp))))
            (posInputs (navW (preNav (Induction.run w₀ x t) (x t).smp))))
          (posInputs (navW (preNav (Induction.run w₀ x t) (x t).smp))) = true →
        Induction.NEGlue w₀ x t) := by
  obtain ⟨P, V, A, hN, hps⟩ := tick_hold_ps _ _ hin hws hst hS hT
  have e : (navW (preNav (Induction.run w₀ x t) (x t).smp)).ps =
      NE_update_controller (preNav (Induction.run w₀ x t) (x t).smp).pp
        (neIn (Induction.run w₀ x t) (x t).smp P V A)
        (posInputs (spoolW (preNav (Induction.run w₀ x t) (x t).smp))) := by
    simp only [hN, neIn]
  refine ⟨P, V, A, e, fun R hD => ?_⟩
  have Eps : (Induction.run w₀ x (t + 1)).ps =
      (D_update_controller (navW (preNav (Induction.run w₀ x t) (x t).smp)).pp
        (NE_update_controller (preNav (Induction.run w₀ x t) (x t).smp).pp
          (neIn (Induction.run w₀ x t) (x t).smp P V A)
          (posInputs (spoolW (preNav (Induction.run w₀ x t) (x t).smp)))) #[]
        (posInputs (navW (preNav (Induction.run w₀ x t) (x t).smp)))).2.1 := by
    rw [show Induction.run w₀ x (t + 1) = (Vehicle.tick (Induction.run w₀ x t) (x t).smp).1 from rfl,
      hps, e]
  obtain ⟨hpid, hpex, hpey, hvex, hvey⟩ := preNav_pid_est (Induction.run w₀ x t) (x t).smp hin
  have pT := Induction.posTarget_run hx t
  have vT := Induction.velTarget_run hx t
  have hA : Induction.accDes w₀ x t = !₂[(Induction.run w₀ x (t + 1)).ps._accel_desired_ned_mss.x.toReal,
      (Induction.run w₀ x (t + 1)).ps._accel_desired_ned_mss.y.toReal,
      (Induction.run w₀ x (t + 1)).ps._accel_desired_ned_mss.z.toReal] := rfl
  have hC : ∀ a, Induction.cmd w₀ x t a = ![(Induction.run w₀ x (t + 1)).ps._accel_target_ned_mss.x.toReal,
      (Induction.run w₀ x (t + 1)).ps._accel_target_ned_mss.y.toReal] a := fun _ => rfl
  have hH : ∀ k a, Induction.habs w₀ x k a = Induction.habs w₀ x k a := fun _ _ => rfl
  clear hH hN hps e
  rw [Eps] at hA hC
  -- the NE call and the D call after it
  obtain ⟨ev, ea, -, -⟩ := ne_desired (preNav (Induction.run w₀ x t) (x t).smp).pp _ _ R.ekf R.active
  obtain ⟨-, -, -, -, q5, -, q7, -⟩ := nS3_eq (neIn (Induction.run w₀ x t) (x t).smp P V A)
    (posInputs (spoolW (preNav (Induction.run w₀ x t) (x t).smp)))
  obtain ⟨px, py⟩ := ne_posd_val hL _ _ _ R
  have F := nef_D (navW (preNav (Induction.run w₀ x t) (x t).smp)).pp
    (NE_update_controller (preNav (Induction.run w₀ x t) (x t).smp).pp
      (neIn (Induction.run w₀ x t) (x t).smp P V A)
      (posInputs (spoolW (preNav (Induction.run w₀ x t) (x t).smp)))) #[]
    (posInputs (navW (preNav (Induction.run w₀ x t) (x t).smp)))
  have s1_pid : (neIn (Induction.run w₀ x t) (x t).smp P V A)._pid_vel_ne_m =
      (Induction.run w₀ x t).ps._pid_vel_ne_m := by
    simp only [neIn, set_pos_vel_accel_NED_m, set_pos_terrain_target_D_m, Id.run, pure]
    exact hpid
  have s1_pex : (neIn (Induction.run w₀ x t) (x t).smp P V A)._pos_estimate_ned_m.x =
      (x t).smp.pos.x := by
    simp only [neIn, set_pos_vel_accel_NED_m, set_pos_terrain_target_D_m, Id.run, pure]
    exact hpex
  have s1_pey : (neIn (Induction.run w₀ x t) (x t).smp P V A)._pos_estimate_ned_m.y =
      (x t).smp.pos.y := by
    simp only [neIn, set_pos_vel_accel_NED_m, set_pos_terrain_target_D_m, Id.run, pure]
    exact hpey
  have s1_vex : (neIn (Induction.run w₀ x t) (x t).smp P V A)._vel_estimate_ned_ms.x =
      (x t).smp.vel.x := by
    simp only [neIn, set_pos_vel_accel_NED_m, set_pos_terrain_target_D_m, Id.run, pure]
    exact hvex
  have s1_vey : (neIn (Induction.run w₀ x t) (x t).smp P V A)._vel_estimate_ned_ms.y =
      (x t).smp.vel.y := by
    simp only [neIn, set_pos_vel_accel_NED_m, set_pos_terrain_target_D_m, Id.run, pure]
    exact hvey
  rw [Eps] at pT vT
  unfold Induction.NEGlue
  refine ⟨(preNav (Induction.run w₀ x t) (x t).smp).pp, neIn (Induction.run w₀ x t) (x t).smp P V A,
    posInputs (spoolW (preNav (Induction.run w₀ x t) (x t).smp)),
    (navW (preNav (Induction.run w₀ x t) (x t).smp)).pp, #[],
    posInputs (navW (preNav (Induction.run w₀ x t) (x t).smp)), R, hD, ?_⟩
  unfold Induction.habs
  rw [Eps]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · unfold axisX
    simp only [posTarget, pT, smpPos, velTarget, vT, smpVel, hA, F.1, F.2.1, F.2.2.1, F.2.2.2.1,
      F.2.2.2.2.1, F.2.2.2.2.2, ev, ea, q5, q7, px, py, s1_pid, s1_pex, s1_vex,
      Matrix.cons_val_zero, WithLp.ofLp_toLp]
  · unfold axisY
    simp only [posTarget, pT, smpPos, velTarget, vT, smpVel, hA, F.1, F.2.1, F.2.2.1, F.2.2.2.1,
      F.2.2.2.2.1, F.2.2.2.2.2, ev, ea, q5, q7, px, py, s1_pid, s1_pey, s1_vey,
      Matrix.cons_val_one, Matrix.cons_val_zero, WithLp.ofLp_toLp]
  all_goals simp only [hC, (thrust_xy _).1, (thrust_xy _).2.1, Matrix.cons_val_zero,
    Matrix.cons_val_one]

end

end Contracts.Track.Reach.Glue
