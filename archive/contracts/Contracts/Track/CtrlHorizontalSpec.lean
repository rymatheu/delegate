import Contracts.Track.CtrlHorizontalNE

/-!
# C-series: the specification of `NE_update_controller` on its region (milestone M6)

`ne_spec`: on `NERegion`, one call of `AC_PosControl::NE_update_controller` is, per axis,
`NEAxis` (the velocity target, the PID rows, the acceleration target against their real rows); the
new `_pid_vel_ne_m` is the PID's (`_reset_filter` stays `false`) and the new limit vector is zero.
-/

namespace Contracts.Track.HCtl

open AC_PosControl_lib Contracts.Quick Contracts.Mission Float.Model UnpackedFloat
open AC_PosControl
open Contracts.Track.Horizontal (αE dtf kpPos kp ki kd)

noncomputable section

theorem nPosTgt_x (s3 : State) :
    (nPosTgt s3).x = s3._pos_desired_ned_m.x + s3._pos_offset_ned_m.x := rfl
theorem nPosTgt_y (s3 : State) :
    (nPosTgt s3).y = s3._pos_desired_ned_m.y + s3._pos_offset_ned_m.y := rfl
theorem nCombPos_x (s3 : State) :
    (nCombPos s3).x = s3._pos_estimate_ned_m.x + Float32.toFloat s3._disturb_pos_ne_m.x := rfl
theorem nCombPos_y (s3 : State) :
    (nCombPos s3).y = s3._pos_estimate_ned_m.y + Float32.toFloat s3._disturb_pos_ne_m.y := rfl
theorem nCombVel_x (s3 : State) :
    (nCombVel s3).x = s3._vel_estimate_ned_ms.x + s3._disturb_vel_ne_ms.x := rfl
theorem nCombVel_y (s3 : State) :
    (nCombVel s3).y = s3._vel_estimate_ned_ms.y + s3._disturb_vel_ne_ms.y := rfl
theorem nVelT_x (p : Params) (s3 : State) (inp : Inputs) :
    (nVelT p s3 inp).x = (nVelP p s3 inp).x + (s3._vel_desired_ned_ms.x + s3._vel_offset_ned_ms.x) :=
  rfl
theorem nVelT_y (p : Params) (s3 : State) (inp : Inputs) :
    (nVelT p s3 inp).y = (nVelP p s3 inp).y + (s3._vel_desired_ned_ms.y + s3._vel_offset_ned_ms.y) :=
  rfl
theorem nAcc_x (p : Params) (s3 : State) (inp : Inputs) :
    (nAcc p s3 inp).x =
      (nAccP p s3 inp).x + (s3._accel_desired_ned_mss.x + s3._accel_offset_ned_mss.x) := rfl
theorem nAcc_y (p : Params) (s3 : State) (inp : Inputs) :
    (nAcc p s3 inp).y =
      (nAccP p s3 inp).y + (s3._accel_desired_ned_mss.y + s3._accel_offset_ned_mss.y) := rfl

theorem lawVt_eq (sp p vsp : ℝ) : lawVt sp p vsp = 3 / 2 * (sp - p) + vsp := by
  simp only [lawVt, kpPos]; norm_num

/-- A `double` position plus a zero offset, and a `double` position plus a widened zero `float`. -/
theorem pos_vals (hL : LibmSpec) {a z : Float} {d : Float32} (ha : a.IsFinite) (hz : z.IsFinite)
    (hz0 : z.toReal = 0) (hd : d.IsFinite) (hd0 : d.toReal = 0) :
    (a + z).IsFinite ∧ (a + z).toReal = a.toReal ∧
      (a + Float32.toFloat d).IsFinite ∧ (a + Float32.toFloat d).toReal = a.toReal := by
  obtain ⟨f1, e1⟩ := hL.f32ToF64 d hd
  exact ⟨(F64.add_zero_val ha hz hz0).1, (F64.add_zero_val ha hz hz0).2,
    (F64.add_zero_val ha f1 (e1.trans hd0)).1, (F64.add_zero_val ha f1 (e1.trans hd0)).2⟩

/-- The velocity target: the P output plus `vsp + 0`. -/
theorem velT_comp {P vd vo : Float32} {d vsp : ℝ} (hP : A32 P (3 / 2 * d) (25 / 10 ^ 8))
    (hd : |d| ≤ 2 / 5) (hvd : FB 3 vd) (hvo : vo.IsFinite) (hvo0 : vo.toReal = 0)
    (hvsp : vd.toReal = vsp) :
    B32 (P + (vd + vo)) (3 / 2 * d + vsp) (5 / 10 ^ 7) (18 / 5) := by
  have bP : B32 P (3 / 2 * d) (25 / 10 ^ 8) (3 / 5) :=
    ⟨hP, by rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 3 / 2)]; linarith⟩
  have bv : B32 (vd + vo) vsp 0 3 :=
    B32.add_zero (B32.lit hvd.1 hvsp (hvsp ▸ hvd.2)) hvo hvo0
  exact B32.add bP bv (by norm_num) (by norm_num [capF]) (by norm_num)

/-- The acceleration target: the PID output plus `asp + 0`. -/
theorem acc_comp {O ad ao : Float32} {asp : ℝ} (hO : FB 89 O) (had : FB 4 ad) (hao : ao.IsFinite)
    (hao0 : ao.toReal = 0) (hasp : ad.toReal = asp) :
    B32 (O + (ad + ao)) (O.toReal + asp) (6 / 10 ^ 6) 93 := by
  have bO : B32 O O.toReal 0 89 := B32.val hO.1 hO.2
  have ba : B32 (ad + ao) asp 0 4 := B32.add_zero (B32.lit had.1 hasp (hasp ▸ had.2)) hao hao0
  exact B32.add bO ba (by norm_num) (by norm_num [capF]) (by norm_num)

set_option maxHeartbeats 4000000 in
/-- **C-series, `NE_update_controller`** on its region: per axis `NEAxis`, the new PID state is
the PID's (`_reset_filter = false`), and the limit vector is zero afterwards. -/
theorem ne_spec (hL : LibmSpec) (p : Params) (s : State) (inp : Inputs) (R : NERegion p s inp) :
    NEAxis (axisX s) (nVelT p (nS3 s inp) inp).x
        (NE_update_controller p s inp)._pid_vel_ne_m._error.x
        (NE_update_controller p s inp)._pid_vel_ne_m._derivative.x
        (NE_update_controller p s inp)._pid_vel_ne_m._integrator.x
        (nPID p (nS3 s inp) inp).2.x (NE_update_controller p s inp)._accel_target_ned_mss.x ∧
      NEAxis (axisY s) (nVelT p (nS3 s inp) inp).y
        (NE_update_controller p s inp)._pid_vel_ne_m._error.y
        (NE_update_controller p s inp)._pid_vel_ne_m._derivative.y
        (NE_update_controller p s inp)._pid_vel_ne_m._integrator.y
        (nPID p (nS3 s inp) inp).2.y (NE_update_controller p s inp)._accel_target_ned_mss.y ∧
      (NE_update_controller p s inp)._pid_vel_ne_m._reset_filter = false ∧
      (NE_update_controller p s inp)._limit_vector_ned.x = Int32.toFloat32 0 ∧
      (NE_update_controller p s inp)._limit_vector_ned.y = Int32.toFloat32 0 := by
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8, q9, q10, q11, q12, -⟩ := nS3_eq s inp
  have off := R.off
  set s3 := nS3 s inp with hs3
  -- positions
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
  -- the P controller
  have hPR : PosRegion ({ x := (nPosTgt s3).x, y := (nPosTgt s3).y } : Vector2p.State)
      (nCombPos s3) := ⟨ftx, fty, fmx, fmy, by simp only [etx, ety, emx, emy]; exact R.e⟩
  have hPg : PosGains p._p_pos_ne_m s3._p_pos_ne_m := q1 ▸ R.posg
  obtain ⟨-, -, hPx, hPy⟩ := p_spec hL p._p_pos_ne_m s3._p_pos_ne_m _ _ hPg hPR
  change A32 (nP p s3).2.2.x _ _ at hPx
  change A32 (nP p s3).2.2.y _ _ at hPy
  simp only [etx, ety, emx, emy] at hPx hPy
  -- the velocity target
  obtain ⟨fVx, eVx, fVy, eVy⟩ := scale2 (v := (nP p s3).2.2) R.scXY.1 R.scXY.2
    (q10 ▸ R.sc.1) (by rw [q10]; exact R.sc.2) hPx.1 hPy.1
  have hPx' : A32 (nVelP p s3 inp).x _ _ := A32.congr_x hPx fVx eVx
  have hPy' : A32 (nVelP p s3 inp).y _ _ := A32.congr_x hPy fVy eVy
  obtain ⟨hdx, hdy⟩ := abs_le_N2 (s._pos_desired_ned_m.x.toReal - s._pos_estimate_ned_m.x.toReal)
    (s._pos_desired_ned_m.y.toReal - s._pos_estimate_ned_m.y.toReal)
  have bVx := velT_comp hPx' (hdx.trans R.e) (q5 ▸ R.vspx) off.vx.1 off.vx.2 (by rw [q5])
  have bVy := velT_comp hPy' (hdy.trans R.e) (q5 ▸ R.vspy) off.vy.1 off.vy.2 (by rw [q5])
  rw [← nVelT_x] at bVx
  rw [← nVelT_y] at bVy
  -- the velocity PID
  have hmx := Float32.add_zero_val (q6 ▸ R.vx.1) (q9 ▸ R.dvx.1) (by rw [q9]; exact R.dvx.2)
  have hmy := Float32.add_zero_val (q6 ▸ R.vy.1) (q9 ▸ R.dvy.1) (by rw [q9]; exact R.dvy.2)
  rw [← nCombVel_x] at hmx
  rw [← nCombVel_y] at hmy
  rw [q6] at hmx hmy
  have pidS : PIDState s3._pid_vel_ne_m s3._limit_vector_ned := q2 ▸ q12 ▸ R.pid
  have hVR : VelRegion s3._pid_vel_ne_m
      (Vector3f.xy ({ s3._vel_target_ned_ms with x := (nVelT p s3 inp).x, y := (nVelT p s3 inp).y }))
      (nCombVel s3) (Vector3f.xy s3._limit_vector_ned) :=
    { reset := pidS.reset
      tx := ⟨bVx.1.1, by have := A32.abs_le' bVx.1; have := bVx.2; show |(nVelT p s3 inp).x.toReal| ≤ 4; linarith⟩
      ty := ⟨bVy.1.1, by have := A32.abs_le' bVy.1; have := bVy.2; show |(nVelT p s3 inp).y.toReal| ≤ 4; linarith⟩
      mx := ⟨hmx.1, by rw [hmx.2]; exact R.vx.2⟩
      my := ⟨hmy.1, by rw [hmy.2]; exact R.vy.2⟩
      Ex := pidS.Ex
      Ey := pidS.Ey
      Dx := pidS.Dx
      Dy := pidS.Dy
      Ix := pidS.Ix
      Iy := pidS.Iy
      I9 := pidS.I9
      limx := pidS.limx
      limy := pidS.limy }
  have hVg : VelGains p._pid_vel_ne_m s3._dt_s := q11 ▸ R.velg
  obtain ⟨-, -, hrst, axX, axY⟩ := pid_spec hL p._pid_vel_ne_m s3._pid_vel_ne_m _ _ _ s3._dt_s hVg hVR
  change PIDAxis (nVelT p s3 inp).x.toReal (nCombVel s3).x.toReal _ _ _ (nPID p s3 inp).1._error.x
    (nPID p s3 inp).1._derivative.x (nPID p s3 inp).1._integrator.x (nPID p s3 inp).2.x at axX
  change PIDAxis (nVelT p s3 inp).y.toReal (nCombVel s3).y.toReal _ _ _ (nPID p s3 inp).1._error.y
    (nPID p s3 inp).1._derivative.y (nPID p s3 inp).1._integrator.y (nPID p s3 inp).2.y at axY
  rw [hmx.2] at axX
  rw [hmy.2] at axY
  rw [q2] at axX axY
  -- the acceleration target
  obtain ⟨fAx, eAx, fAy, eAy⟩ := scale2 (v := (nPID p s3 inp).2) R.scXY.1 R.scXY.2
    (q10 ▸ R.sc.1) (by rw [q10]; exact R.sc.2) axX.2.2.2.1.1 axY.2.2.2.1.1
  have bAx := acc_comp ⟨fAx, by rw [eAx]; exact axX.2.2.2.2.2.2.2⟩ (q7 ▸ R.aspx) off.ax.1 off.ax.2
    (by rw [q7])
  have bAy := acc_comp ⟨fAy, by rw [eAy]; exact axY.2.2.2.2.2.2.2⟩ (q7 ▸ R.aspy) off.ay.1 off.ay.2
    (by rw [q7])
  change B32 (nAcc p s3 inp).x _ _ _ at bAx
  change B32 (nAcc p s3 inp).y _ _ _ at bAy
  rw [eAx] at bAx
  rw [eAy] at bAy
  -- the limiter is inactive
  have vX : A32 (nVelT p s3 inp).x (lawVt (axisX s).sp (axisX s).p (axisX s).vsp) (5 / 10 ^ 7) :=
    bVx.1.congr (lawVt_eq _ _ _).symm
  have vY : A32 (nVelT p s3 inp).y (lawVt (axisY s).sp (axisY s).p (axisY s).vsp) (5 / 10 ^ 7) :=
    bVy.1.congr (lawVt_eq _ _ _).symm
  have cx := rows_compose vX.2 axX.1.2 axX.2.1.2 axX.2.2.1.2 axX.2.2.2.1.2 bAx.1.2
  have cy := rows_compose vY.2 axY.1.2 axY.2.1.2 axY.2.2.1.2 axY.2.2.2.1.2 bAy.1.2
  have hA : nAmax p s3 inp = nAmax p s inp := nAmax_eq p s inp
  have hNacc : N2 (nAcc p s3 inp).x.toReal (nAcc p s3 inp).y.toReal ≤
      (nAmax p s3 inp).toReal * (1 - 1 / 2 ^ 20) := by
    have h1 := N2_le_near (nAcc p s3 inp).x.toReal (nAcc p s3 inp).y.toReal (axisX s).c (axisY s).c
    have h2 := cx.2.2.2
    have h3 := cy.2.2.2
    have h4 := R.lim
    rw [hA]
    simp only [AxisIn.c, axisX, axisY] at h1 h2 h3 h4
    linarith
  have bx : |(nAcc p s3 inp).x.toReal| ≤ 2 ^ 40 := by
    have := A32.abs_le' bAx.1; have := bAx.2; linarith
  have byy : |(nAcc p s3 inp).y.toReal| ≤ 2 ^ 40 := by
    have := A32.abs_le' bAy.1; have := bAy.2; linarith
  have HL : ∀ v, limit_accel_xy v (nAcc p s3 inp) (nAmax p s3 inp) = (nAcc p s3 inp, false) :=
    fun v => limit_accel_xy_inactive v _ _ bAx.1.1 bAy.1.1 bx byy (hA ▸ R.amax.1)
      (by rw [hA]; exact R.amax.2.1) (by rw [hA]; exact R.amax.2.2) hNacc
  obtain ⟨o1, o2, o3, o4⟩ := ne_out p s inp R.ekf R.active HL
  have hpid := ne_pid p s inp R.ekf R.active
  refine ⟨⟨vX, ?_, ?_⟩, ⟨vY, ?_, ?_⟩, ?_, o3, o4⟩
  · rw [hpid]; exact axX
  · rw [o1]; exact bAx.1
  · rw [hpid]; exact axY
  · rw [o2]; exact bAy.1
  · rw [hpid]; exact hrst

end

end Contracts.Track.HCtl
