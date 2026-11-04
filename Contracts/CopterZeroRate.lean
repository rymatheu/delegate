import Contracts.CopterZeroAtt
import AC_AttitudeControl.AC_AttitudeControl_Multi

/-!
# Zero lemmas for `AC_AttitudeControl_Multi`

- `rate_controller_run_dt_Z`: with a zero rate target `_ang_vel_body_rads`, a zero gyro and the
  rate PIDs at zero, the roll, pitch and yaw inputs and feed-forwards written to the motors are
  zeros and the PIDs stay at zero, for every throttle slew rate (the gain boost multiplies the PD
  scale by a factor in `[1, 2]`).
- `get_throttle_boosted_id`: with `cos_pitch = cos_roll = 1` and a zero thrust angle the angle boost
  is the identity on the throttle (`cosf(0) = 1`, libm) and `_angle_boost` is a zero.
-/

open Float.Model UnpackedFloat AP_Math AC_AttitudeControl_Multi

namespace Contracts.CopterZero

/-! ## Throttle boost -/

theorem lit_one_ten : (10.0 : Float32).IsFinite ∧ (10.0 : Float32).toReal = 10 := lit_ten

/-- **`get_throttle_boosted` at a level attitude**: with `cos_pitch`, `cos_roll` of value one and a
zero `_thrust_angle_rad`, the boosted throttle is the throttle (in value) and `_angle_boost` is a
zero. Uses `cosf(±0) = 1`. -/
theorem get_throttle_boosted_id (L : LibmZero32) (p : Params) (s : State)
    {cos_pitch cos_roll throttle_in : Float32} (hcp : One cos_pitch) (hcr : One cos_roll)
    (hta : Z s._thrust_angle_rad) (ht : throttle_in.IsFinite) :
    (get_throttle_boosted p s cos_pitch cos_roll throttle_in).2.IsFinite ∧
      (get_throttle_boosted p s cos_pitch cos_roll throttle_in).2.toReal = throttle_in.toReal ∧
      Z (get_throttle_boosted p s cos_pitch cos_roll throttle_in).1._angle_boost := by
  unfold get_throttle_boosted
  split
  · exact ⟨ht, rfl, Z_zero⟩
  · simp only []
    have hct := One_mul hcp hcr
    have h10 := mul_exact lit_ten.1 hct.1 lit_ten.1 (by rw [hct.2, mul_one])
    have hinv : One (constrain_float (10.0 * (cos_pitch * cos_roll)) 0.0 1.0) := by
      have := constrain_above h10.1 Z_lit0.1 lit_one.1 (by rw [Z_lit0.2, lit_one.2]; norm_num)
        (by rw [h10.2, lit_ten.2, lit_one.2]; norm_num)
      exact ⟨this.1, this.2.trans lit_one.2⟩
    have hcos := L.cos_zero _ hta
    have hcl : One (constrain_float (Float32.cos s._thrust_angle_rad) 0.1 1.0) := by
      obtain ⟨h1, h2, h3⟩ := lit_tenth
      have := constrain_in hcos.1 h1 lit_one.1 (by rw [hcos.2]; linarith)
        (by rw [hcos.2, lit_one.2])
      exact ⟨this.1, this.2.trans hcos.2⟩
    have hbf := One_div lit_one hcl
    have h1 := mul_One_right ht hinv
    have h2 := mul_One_right h1.1 hbf
    have hout : (throttle_in * constrain_float (10.0 * (cos_pitch * cos_roll)) 0.0 1.0 *
        (1.0 / constrain_float (Float32.cos s._thrust_angle_rad) 0.1 1.0)).toReal =
        throttle_in.toReal := h2.2.trans h1.2
    refine ⟨h2.1, hout, ?_⟩
    have hd := sub_exact h2.1 ht Float32.isFinite_zero (by rw [hout, sub_self, Float32.toReal_zero])
    have hd' : Z (throttle_in * constrain_float (10.0 * (cos_pitch * cos_roll)) 0.0 1.0 *
        (1.0 / constrain_float (Float32.cos s._thrust_angle_rad) 0.1 1.0) - throttle_in) :=
      ⟨hd.1, hd.2.trans Float32.toReal_zero⟩
    exact constrain_Z hd' lit_neg_one.1 lit_one.1 (by rw [lit_neg_one.2]; norm_num)
      (by rw [lit_one.2]; norm_num)

/-! ## The rate controller -/

/-- The gain-boost factors `constrain_float(·, 1, 2)` and `constrain_float(·, 1, 4)` are finite
and in `[1, 4]`. -/
theorem boost_spec (x : Float32) {hi : Float32} (hhi : hi.IsFinite ∧ hi.toReal ≤ 4 ∧ 1 ≤ hi.toReal) :
    (constrain_float x 1.0 hi).IsFinite ∧ |(constrain_float x 1.0 hi).toReal| ≤ 4 := by
  rw [constrain_float_eq]
  have hsum : |(1.0 : Float32).toReal + hi.toReal| ≤ maxFinite32 := by
    have := maxFinite32_ge
    rw [lit_one.2, abs_le]; constructor <;> linarith
  obtain ⟨h1, h2, h3⟩ := Contracts.Float32Clip.constrain_float_spec lit_one.1 hhi.1
    (by rw [lit_one.2]; exact hhi.2.2) hsum x
  rw [lit_one.2] at h2
  exact ⟨h1, by rw [abs_le]; constructor <;> linarith⟩

/-- A PD scale component of magnitude at most `10³⁰` stays finite after the boost. -/
theorem scale_boost_fin {c b : Float32} (hc : c.IsFinite) (hcb : |c.toReal| ≤ 1e30)
    (hb : b.IsFinite) (hbb : |b.toReal| ≤ 4) : (c * b).IsFinite :=
  fin_mul hc hb (by rw [abs_mul]; nlinarith [abs_nonneg c.toReal, abs_nonneg b.toReal])

/-- What the rate controller reads of the state after `update_throttle_gain_boost` and
`update_throttle_rpy_mix`: the PID states, the system-identification offsets, the I scale and the
feed-forward scalar are unchanged, and the PD scale is finite. -/
theorem prep_fields (p : Params) (s : State) (m : AP_Motors.Inputs) (slew : Float32)
    (hpd : s._pd_scale.x.IsFinite ∧ s._pd_scale.y.IsFinite ∧ s._pd_scale.z.IsFinite)
    (hpdb : |s._pd_scale.x.toReal| ≤ 1e30 ∧ |s._pd_scale.y.toReal| ≤ 1e30) :
    let s1 := update_throttle_rpy_mix (update_throttle_gain_boost p s slew) m
    s1._pid_rate_roll = s._pid_rate_roll ∧ s1._pid_rate_pitch = s._pid_rate_pitch ∧
      s1._pid_rate_yaw = s._pid_rate_yaw ∧
      s1._sysid_ang_vel_body_rads = s._sysid_ang_vel_body_rads ∧
      s1._actuator_sysid = s._actuator_sysid ∧ s1._i_scale = s._i_scale ∧
      s1._feedforward_scalar = s._feedforward_scalar ∧
      s1._pd_scale.x.IsFinite ∧ s1._pd_scale.y.IsFinite ∧ s1._pd_scale.z.IsFinite := by
  intro s1
  unfold s1 update_throttle_rpy_mix update_throttle_gain_boost
  split
  · simp only [lift, AC_AttitudeControl.set_PD_scale_mult, AC_AttitudeControl.set_angle_P_scale_mult,
      AC_AttitudeControl.vec_mul_assign]
    obtain ⟨b1, b2⟩ := boost_spec (p.ATC_THR_G_BOOST + 1.0) (hi := 2.0)
      ⟨lit_two.1, by rw [lit_two.2]; norm_num, by rw [lit_two.2]; norm_num⟩
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, scale_boost_fin hpd.1 hpdb.1 b1 b2,
      scale_boost_fin hpd.2.1 hpdb.2 b1 b2, (mul_One_right hpd.2.2 lit_one).1⟩
    all_goals trivial
  · exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, hpd⟩

/-- Rate PID gains as `PidOK`. -/
structure RatePidsOK (p : Params) : Prop where
  roll : PidOK p.ATC_RAT_RLL
  pitch : PidOK p.ATC_RAT_PIT
  yaw : PidOK p.ATC_RAT_YAW

/-- **`rate_controller_run_dt` at zero.** With a zero rate target `_ang_vel_body_rads`, zero
system-identification offsets, a zero gyro, the three rate PIDs at zero, a finite PD scale of
magnitude at most `10³⁰`, a finite I scale and feed-forward scalar, and a finite
`|dt| ≤ 10³⁰`: the six motor inputs `_roll_in`, `_pitch_in`, `_yaw_in`, `_roll_in_ff`,
`_pitch_in_ff`, `_yaw_in_ff` are zeros, the three PIDs stay at zero, and the gyro is stored. -/
theorem rate_controller_run_dt_Z (p : Params) (hp : RatePidsOK p) (s : State)
    (hbody : ZV s._ang_vel_body_rads) (hsys : ZV s._sysid_ang_vel_body_rads)
    (hact : ZV s._actuator_sysid) (hr : ZPID s._pid_rate_roll) (hq : ZPID s._pid_rate_pitch)
    (hy : ZPID s._pid_rate_yaw)
    (hpd : s._pd_scale.x.IsFinite ∧ s._pd_scale.y.IsFinite ∧ s._pd_scale.z.IsFinite)
    (hpdb : |s._pd_scale.x.toReal| ≤ 1e30 ∧ |s._pd_scale.y.toReal| ≤ 1e30)
    (hi : s._i_scale.x.IsFinite ∧ s._i_scale.y.IsFinite ∧ s._i_scale.z.IsFinite)
    (hff : s._feedforward_scalar.IsFinite) (m : AP_Motors.Inputs) (slew : Float32)
    {gyro : Vector3f} (hg : ZV gyro) {dt : Float32} (hdt : dt.IsFinite) (hdtb : |dt.toReal| ≤ 1e30) :
    let r := rate_controller_run_dt p s m slew gyro dt
    Z r.2._roll_in ∧ Z r.2._pitch_in ∧ Z r.2._yaw_in ∧
      Z r.2._roll_in_ff ∧ Z r.2._pitch_in_ff ∧ Z r.2._yaw_in_ff ∧
      ZPID r.1._pid_rate_roll ∧ ZPID r.1._pid_rate_pitch ∧ ZPID r.1._pid_rate_yaw ∧
      r.1._rate_gyro_rads = gyro := by
  intro r
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, f1, f2, f3⟩ := prep_fields p s m slew hpd hpdb
  unfold r rate_controller_run_dt
  simp only [AP_Motors.set_roll, AP_Motors.set_roll_ff, AP_Motors.set_pitch, AP_Motors.set_pitch_ff,
    AP_Motors.set_yaw, AP_Motors.set_yaw_ff]
  generalize update_throttle_rpy_mix (update_throttle_gain_boost p s slew) m = s1 at *
  simp only [e1, e2, e3, e4, e5, e6, e7]
  have hab := ZV_add hbody hsys
  obtain ⟨R1, R2, R3⟩ := pid_update_all_Z _ hp.roll hr (target := (s._ang_vel_body_rads +
    s._sysid_ang_vel_body_rads).x) hab.1 hg.1 hdt hdtb m.limit.roll f1 hi.1
  obtain ⟨Q1, Q2, Q3⟩ := pid_update_all_Z _ hp.pitch hq (target := (s._ang_vel_body_rads +
    s._sysid_ang_vel_body_rads).y) hab.2.1 hg.2.1 hdt hdtb m.limit.pitch f2 hi.2.1
  obtain ⟨Y1, Y2, Y3⟩ := pid_update_all_Z _ hp.yaw hy (target := (s._ang_vel_body_rads +
    s._sysid_ang_vel_body_rads).z) hab.2.2 hg.2.2 hdt hdtb m.limit.yaw f3 hi.2.2
  exact ⟨Z_add R2 hact.1, Z_add Q2 hact.2.1, Z_add Y2 hact.2.2, R3, Q3, Z_mul_left Y3 hff,
    R1, Q1, Y1, trivial⟩

end Contracts.CopterZero
