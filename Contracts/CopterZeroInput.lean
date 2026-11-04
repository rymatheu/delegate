import Contracts.CopterZeroAtt

/-!
# Zero lemma for `AC_AttitudeControl::input_thrust_vector_heading_rad`

The thrust-vector entry point called by Auto at the hover sample: thrust vector
`(±0, ±0, -GRAVITY_MSS)`, zero heading and heading rate, identity body and target, zero shaping
state. It chains `update_attitude_target` (`update_attitude_target_Id`), the target Euler angles
(`to_euler_vec_Id`: `atan2f`, `asinf` at zero), `attitude_from_thrust_vector`,
`thrust_vector_rotation_angles`, three `attitude_command_model` calls,
`body_to_euler_derivative` (`sinf`, `cosf` at zero) and `attitude_controller_run_quat`. All five
libm facts are used here.
-/

open Float.Model UnpackedFloat AP_Math AC_AttitudeControl

namespace Contracts.CopterZero

/-- `update_attitude_target` with a zero target rate keeps an identity target. -/
theorem update_attitude_target_Id (s : AC_AttitudeControl.State) (ht : IdQ s._attitude_target)
    (hv : ZV s._ang_vel_target_rads) (hdt : s._dt_s.IsFinite) :
    IdQ (update_attitude_target s)._attitude_target := by
  unfold update_attitude_target
  simp only []
  rw [from_axis_angle_Z (ZV_mul hv hdt)]
  exact normalize_Id (mul_Id ht IdQ_lit)

theorem two_Z {x : Float32} (hx : Z x) : Z (2.0 * x) := Z_mul_right lit_two.1 hx

/-- The Euler angles of the identity are zeros (`atan2f(±0, 1) = ±0`, `asinf(±0) = ±0`). -/
theorem to_euler_vec_Id (L : LibmZero32) {q : Quaternion} (h : IdQ q) : ZV q.to_euler_vec := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hden : ∀ a b : Float32, Z a → Z b →
      (1.0 - 2.0 * (a * a + b * b)).IsFinite ∧ 0 < (1.0 - 2.0 * (a * a + b * b)).toReal := by
    intro a b ha hb
    have := One_sub_Z lit_one (two_Z (Z_add (Z_mul_left ha ha.1) (Z_mul_left hb hb.1)))
    exact ⟨this.1, by rw [this.2]; norm_num⟩
  refine ⟨?_, ?_, ?_⟩
  · obtain ⟨d1, d2⟩ := hden q.q2 q.q3 h2 h3
    exact L.atan2_zero _ _ (two_Z (Z_add (Z_mul_right h1.1 h2) (Z_mul_left h3 h4.1))) d1 d2
  · show Z (safe_asin (2.0 * (q.q1 * q.q3 - q.q4 * q.q2)))
    have hz := two_Z (Z_sub (Z_mul_right h1.1 h3) (Z_mul_left h4 h2.1))
    unfold safe_asin
    rw [isNaN_false hz.1]
    have c1 : ¬ (2.0 * (q.q1 * q.q3 - q.q4 * q.q2) ≥ 1.0) := by
      rw [ge_iff_le, le_iff lit_one.1 hz.1, hz.2, lit_one.2]; norm_num
    have c2 : ¬ (2.0 * (q.q1 * q.q3 - q.q4 * q.q2) ≤ -1.0) := by
      rw [le_iff hz.1 lit_neg_one.1, hz.2, lit_neg_one.2]; norm_num
    simp only [Bool.false_eq_true, if_false, c1, c2]
    exact L.asin_zero _ hz
  · obtain ⟨d1, d2⟩ := hden q.q3 q.q4 h3 h4
    exact L.atan2_zero _ _ (two_Z (Z_add (Z_mul_right h1.1 h4) (Z_mul_left h2 h3.1))) d1 d2

/-- `body_to_euler_derivative` at the identity attitude maps a zero body rate to a zero Euler-rate
vector (`sinf(0) = 0`, `cosf(0) = 1`, so `is_zero(cos θ)` is false). -/
theorem body_to_euler_derivative_Id (L : LibmZero32) {q : Quaternion} (h : IdQ q) {w : Vector3f}
    (hw : ZV w) (e : Vector3f) : ZV (body_to_euler_derivative q w e).1 := by
  obtain ⟨er, ep, -⟩ := to_euler_vec_Id L h
  change Z q.get_euler_roll at er
  change Z q.get_euler_pitch at ep
  have sp := L.sin_zero _ ep
  have cp := L.cos_zero _ ep
  have sr := L.sin_zero _ er
  have cr := L.cos_zero _ er
  unfold body_to_euler_derivative
  simp only []
  rw [is_zero_One cp]
  simp only [Bool.false_eq_true, if_false]
  have q1 := Z_div sp cp.1 (by rw [cp.2]; norm_num)
  have q2 := Z_div sr cp.1 (by rw [cp.2]; norm_num)
  have q3 := div_One_right cr.1 cp
  exact ⟨Z_add (Z_add hw.1 (Z_mul_left (Z_mul_right sr.1 q1) hw.2.1.1))
      (Z_mul_right (Z_mul_right cr.1 q1).1 hw.2.2),
    Z_sub (Z_mul_right cr.1 hw.2.1) (Z_mul_right sr.1 hw.2.2),
    Z_add (Z_mul_left q2 hw.2.1.1) (Z_mul_right q3.1 hw.2.2)⟩

/-- Limits read by the shaping of `input_thrust_vector_heading_rad`: finite acceleration limits of
magnitude at most `1000` rad/s², finite time constants and slew limit, `|dt| ≤ 10¹⁸`. -/
structure InputOK (p : AC_AttitudeControl.Params) (s : AC_AttitudeControl.State) : Prop where
  accr : (get_accel_roll_max_radss p).IsFinite
  accp : (get_accel_pitch_max_radss p).IsFinite
  accy : (get_accel_yaw_max_radss p).IsFinite
  accrb : |(get_accel_roll_max_radss p).toReal| ≤ 1000
  accpb : |(get_accel_pitch_max_radss p).toReal| ≤ 1000
  accyb : |(get_accel_yaw_max_radss p).toReal| ≤ 1000
  tc : p._input_tc.IsFinite
  ytc : s._rate_y_tc.IsFinite
  slew : (get_slew_yaw_max_rads p).IsFinite
  dt : s._dt_s.IsFinite
  dtb : |s._dt_s.toReal| ≤ 1e18

/-- **`input_thrust_vector_heading_rad` at the hover sample.** Thrust vector `(±0, ±0, -g)`, zero
heading and heading rate, identity body and target, zero target rate and acceleration: the body-rate
demand is a zero, the target stays at the identity, the thrust angles are zeros, and the target rate
and acceleration stay zeros, with or without `ATC_RATE_FF_ENAB`. Uses all five libm facts. -/
theorem input_thrust_vector_heading_rad_Z (L : LibmZero32) (C : ConvZero)
    (p : AC_AttitudeControl.Params) (get_rate_yaw_pid : AC_PID.Params)
    (hcap : ¬ (yaw_error_cap p get_rate_yaw_pid < 0)) (hrm : RateMaxOK p)
    (s : AC_AttitudeControl.State) (hang : AngOK p s) (hin : InputOK p s)
    (ht : IdQ s._attitude_target) (hv : ZV s._ang_vel_target_rads)
    (ha : ZV s._ang_accel_target_rads) {body : Quaternion} (hb : IdQ body) {tv : Vector3f}
    (hx : Z tv.x) (hy : Z tv.y) (hz : tv.z = -GRAVITY_MSS) {heading heading_rate : Float32}
    (hh : Z heading) (hhr : Z heading_rate) :
    let r := input_thrust_vector_heading_rad p get_rate_yaw_pid s body tv heading heading_rate
    ZV r._ang_vel_body_rads ∧ IdQ r._attitude_target ∧ Z r._thrust_angle_rad ∧
      Z r._thrust_error_angle_rad ∧ ZV r._ang_vel_target_rads ∧ ZV r._ang_accel_target_rads ∧
      ZV r._euler_rate_target_rads := by
  intro r
  unfold r input_thrust_vector_heading_rad
  simp (config := {zeta := false}) only []
  extract_lets s4 s3 dq s2 s1 s0
  have ht3 : IdQ s3._attitude_target := update_attitude_target_Id s ht hv hin.dt
  have hv3 : ZV s3._ang_vel_target_rads := hv
  have ha3 : ZV s3._ang_accel_target_rads := ha
  have hdq : IdQ dq := attitude_from_thrust_vector_Id L hx hy hz hh
  obtain ⟨rf, -⟩ := radians_nonneg hrm.roll.1 hrm.roll.2.1 hrm.roll.2.2
  obtain ⟨qf, -⟩ := radians_nonneg hrm.pitch.1 hrm.pitch.2.1 hrm.pitch.2.2
  have H1 : IdQ s1._attitude_target ∧ ZV s1._ang_vel_target_rads ∧
      ZV s1._ang_accel_target_rads ∧ s1._angle_P_scale = s._angle_P_scale ∧ s1._dt_s = s._dt_s := by
    simp only [s1]
    split
    · have E := (thrust_vector_rotation_angles_Id L hdq ht3).2.1
      have cx := attitude_command_model_Z C E.1 Z_lit0 hv3.1 ha3.1 rf hin.accr hin.tc hin.dt
        hin.accrb hin.dtb
      have cy := attitude_command_model_Z C E.2.1 Z_lit0 hv3.2.1 ha3.2.1 qf hin.accp hin.tc hin.dt
        hin.accpb hin.dtb
      have cz := attitude_command_model_Z C E.2.2 hhr hv3.2.2 ha3.2.2 hin.slew hin.accy hin.ytc
        hin.dt hin.accyb hin.dtb
      exact ⟨ht3, ⟨cx.1, cy.1, cz.1⟩, ⟨cx.2, cy.2, cz.2⟩, rfl, rfl⟩
    · exact ⟨hdq, ⟨Z_zero, Z_zero, Z_zero⟩, ⟨Z_zero, Z_zero, Z_zero⟩, rfl, rfl⟩
  obtain ⟨h1, h2, h3, h4, h5⟩ := H1
  have h0t : IdQ s0._attitude_target := h1
  have h0v : ZV s0._ang_vel_target_rads := h2
  have h0e : ZV s0._euler_rate_target_rads :=
    body_to_euler_derivative_Id L h1 h2 s1._euler_rate_target_rads
  have hang0 : AngOK p s0 := by
    have e4 : s0._angle_P_scale = s._angle_P_scale := h4
    have e5 : s0._dt_s = s._dt_s := h5
    exact ⟨hang.kr, hang.kp, hang.ky, hang.krb, hang.kpb, hang.kyb, e4 ▸ hang.sx, e4 ▸ hang.sy,
      e4 ▸ hang.sz, e4 ▸ hang.sxb, e4 ▸ hang.syb, e4 ▸ hang.szb, e5 ▸ hang.dt⟩
  obtain ⟨R1, R2, R3, R4, -, -, R7, R8, R9, -⟩ :=
    attitude_controller_run_quat_Z L p get_rate_yaw_pid hcap hrm s0 hang0 h0t h0v hb
  refine ⟨R1, R2 ▸ h0t, R3, R4, R7 ▸ h0v, R8 ▸ (h3 : ZV s0._ang_accel_target_rads), R9 ▸ h0e⟩

end Contracts.CopterZero
