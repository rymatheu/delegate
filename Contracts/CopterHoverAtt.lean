import Contracts.CopterZeroInput
import Contracts.CopterZeroRate
import Contracts.CopterHoverUniverse

/-!
# The attitude path at the hover fixed point

The pieces of one tick of the hover run that act on the attitude and the AHRS, at the hover fixed
point (level, identity attitude, zero rates):

- `ahrs_update_level`: `AHRS.update` on the identity quaternion. The rotation matrix and
  `calc_trig` are concrete and evaluated by the kernel (`calc_trig_level`); the two `sqrtf(1)`
  calls go through `Nat.sqrt`, which is well-founded recursion and is supplied for the one
  argument `2⁴⁶` (`natSqrt_one`, `sqrt_key`). The Euler angles go through `atan2f(±0, 1)` and
  `asinf(±0)` (`LibmZero32`).
- `input_thrust_vector_rate_heading_rads_Z`: the `Rate_Only` thrust-vector entry (AutoYaw
  `HOLD`), the analogue of `CopterZero.input_thrust_vector_heading_rad_Z`;
  `input_thrust_vector_heading_rad_Z_full` adds the Euler-angle target and the feed-forward
  scalar to that lemma. The frames `input_thrust_vector_rate_heading_rads_frame`,
  `input_thrust_vector_heading_rad_frame` list the ten fields the two entries write; the Multi
  wrappers `multi_rate_only_Z`, `multi_angle_and_rate_Z` keep the rate PID states.
- `get_heading_hold`, `get_heading_next_wp`: `AutoYaw.get_heading` in the two modes of the run.
- `run_rate_controller_main_Z`: the rate-controller stage of the tick, with the facts about
  `runParams` it needs and those the attitude lemmas need (`runParams_ratePidsOK`,
  `runParams_rateMaxOK`, `runParams_cap`, `runParams_inputOK`, `runParams_angOK`), all decided by
  the kernel on the concrete parameter literals.
-/

open Float.Model UnpackedFloat AP_Math Contracts.CopterZero AC_AttitudeControl
open Contracts.CopterVertNear (dtF dtF_val)

namespace Contracts.CopterHover

/-! ## The AHRS at a level attitude -/

/-- The integer square root inside `sqrtf(1)`: `⌊√(2⁴⁶)⌋ = 2²³`. -/
theorem natSqrt_one : Nat.sqrt 70368744177664 = 8388608 := by
  symm; rw [Nat.eq_sqrt]; constructor <;> norm_num

/-- `sqrtf(x) = 1` for every `x` with the unpacked form of `1` (computed by the kernel, with
`Nat.sqrt` supplied by `natSqrt_one`). -/
theorem sqrt_one_of {x : Float32}
    (h : x.toModel.unpack = .finite .positive 8388608 (-23) (by decide)) : Float32.sqrt x = 1 := by
  have key : ∀ n, Nat.sqrt n = if n = 70368744177664 then 8388608 else Nat.sqrt n := by
    intro n; split
    · subst_vars; exact natSqrt_one
    · rfl
  show Float32.ofModel
    (Float32.Model.pack (UnpackedFloat.sqrt Format.binary32 x.toModel.unpack)) = 1
  rw [h]
  simp only [UnpackedFloat.sqrt, UnpackedFloat.sqrtCore]
  rw [key]
  decide

/-- `sqrtf` rewritten so that the kernel can evaluate it at `1` without `Nat.sqrt`. -/
theorem sqrt_key : Float32.sqrt = fun x => if x = 1 then 1 else Float32.sqrt x := by
  funext x; split
  · subst_vars; exact sqrt_one_of rfl
  · rfl

/-- **`calc_trig` of the identity rotation matrix** is `(cr, cp, cy, sr, sp, sy) = (1, 1, 1, +0,
-0, +0)`, bit for bit (no fallback through `to_euler`). -/
theorem calc_trig_level : Copter.AHRS.calc_trig (Quaternion.rotation_matrix ⟨1, 0, 0, 0⟩) =
    (1, 1, 1, 0, -0, 0) := by
  unfold Copter.AHRS.calc_trig safe_sqrt Vector2f.normalize Vector2f.length AP_Math.norm
  rw [sqrt_key]
  decide


/-- The entries of the identity's rotation matrix that `to_euler` reads. -/
theorem rot_level :
    (Quaternion.rotation_matrix ⟨1, 0, 0, 0⟩).c.x = 0 ∧
      (Quaternion.rotation_matrix ⟨1, 0, 0, 0⟩).c.y = 0 ∧
      (Quaternion.rotation_matrix ⟨1, 0, 0, 0⟩).c.z = 1 ∧
      (Quaternion.rotation_matrix ⟨1, 0, 0, 0⟩).b.x = 0 ∧
      (Quaternion.rotation_matrix ⟨1, 0, 0, 0⟩).a.x = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- `safe_asin(+0)` is a zero (`asinf(±0) = ±0`). -/
theorem safe_asin_zero (L : LibmZero32) : Z (safe_asin (0 : Float32)) := by
  unfold safe_asin
  have h1 : (0 : Float32).isNaN = false := by decide
  have h2 : ¬ ((0 : Float32) ≥ 1.0) := by decide
  have h3 : ¬ ((0 : Float32) ≤ -1.0) := by decide
  simp only [h1, h2, h3, Bool.false_eq_true, if_false]
  exact L.asin_zero _ Z_zero

/-- **`AHRS.update` at a level attitude.** For the identity quaternion `⟨1, 0, 0, 0⟩` the
cosines are one, the sines and the Euler angles zeros (`sin_pitch` is `-0`), the quaternion is the
identity, and the other readings are passed through. Uses `atan2f` and `asinf` at zero. -/
theorem ahrs_update_level (L : LibmZero32) (smp : Copter.AHRS.Sample)
    (hq : smp.quat = ⟨1, 0, 0, 0⟩) :
    let v := Copter.AHRS.update smp
    One v.cos_pitch ∧ One v.cos_roll ∧ One v.cos_yaw ∧ Z v.sin_yaw ∧ Z v.sin_roll ∧ Z v.sin_pitch ∧
      Z v.roll ∧ Z v.pitch ∧ Z v.yaw ∧ IdQ v.quat_body_to_ned ∧ v.quat_body_to_ned = smp.quat ∧
      v.accel_ef = smp.accel_ef ∧ v.pos_ned = smp.pos ∧ v.vel_ned = smp.vel ∧
      v.gyro_latest = smp.gyro := by
  intro v
  obtain ⟨r1, r2, r3, r4, r5⟩ := rot_level
  have hpos : (0 : ℝ) < (1 : Float32).toReal := by rw [Float32.toReal_one]; norm_num
  simp only [v, Copter.AHRS.update, hq, calc_trig_level, Matrix3f.to_euler, r1, r2, r3, r4, r5]
  refine ⟨One_one, One_one, One_one, Z_zero, Z_zero, Z_neg Z_zero,
    L.atan2_zero _ _ Z_zero Float32.isFinite_one hpos, Z_neg (safe_asin_zero L),
    L.atan2_zero _ _ Z_zero Float32.isFinite_one hpos,
    ⟨One_one, Z_zero, Z_zero, Z_zero⟩, trivial, trivial, trivial, trivial, trivial⟩

/-! ## Rate-heading thrust vector entry -/

/-- **`input_thrust_vector_rate_heading_rads` at the hover sample** (the `Rate_Only` entry, AutoYaw
`HOLD`). Thrust vector `(±0, ±0, -g)`, zero heading rate, identity body and target, zero target rate
and acceleration: the body-rate demand is a zero, the target stays at the identity, the thrust
angles are zeros, the target rate, acceleration, Euler rates and Euler angles are zeros and the
feed-forward scalar is `1.0`, with or without `ATC_RATE_FF_ENAB` and for both `slew_yaw`. The
hypotheses are those of `CopterZero.input_thrust_vector_heading_rad_Z`. -/
theorem input_thrust_vector_rate_heading_rads_Z (L : LibmZero32) (C : ConvZero)
    (p : AC_AttitudeControl.Params) (get_rate_yaw_pid : AC_PID.Params)
    (hcap : ¬ (yaw_error_cap p get_rate_yaw_pid < 0)) (hrm : RateMaxOK p)
    (s : AC_AttitudeControl.State) (hang : AngOK p s) (hin : InputOK p s)
    (ht : IdQ s._attitude_target) (hv : ZV s._ang_vel_target_rads)
    (ha : ZV s._ang_accel_target_rads) {body : Quaternion} (hb : IdQ body) {tv : Vector3f}
    (hx : Z tv.x) (hy : Z tv.y) (hz : tv.z = -GRAVITY_MSS) {heading_rate : Float32}
    (hhr : Z heading_rate) (slew_yaw : Bool) :
    let r := AC_AttitudeControl.input_thrust_vector_rate_heading_rads p get_rate_yaw_pid s body tv
      heading_rate slew_yaw
    ZV r._ang_vel_body_rads ∧ IdQ r._attitude_target ∧ Z r._thrust_angle_rad ∧
      Z r._thrust_error_angle_rad ∧ ZV r._ang_vel_target_rads ∧ ZV r._ang_accel_target_rads ∧
      ZV r._euler_rate_target_rads ∧ ZV r._euler_angle_target_rad ∧
      r._feedforward_scalar = 1.0 := by
  intro r
  unfold r input_thrust_vector_rate_heading_rads
  simp (config := {zeta := false}) only []
  extract_lets ym0 ym s4 s3 tq hrr yq at2 s2 s1 s0
  have ht3 : IdQ s3._attitude_target := update_attitude_target_Id s ht hv hin.dt
  have he3 : ZV s3._euler_angle_target_rad := to_euler_vec_Id L ht3
  have hv3 : ZV s3._ang_vel_target_rads := hv
  have ha3 : ZV s3._ang_accel_target_rads := ha
  have hdq : IdQ tq := attitude_from_thrust_vector_Id L hx hy hz Z_lit0
  obtain ⟨E0, E, -, -⟩ := thrust_vector_rotation_angles_Id L hdq ht3
  obtain ⟨rf, -⟩ := radians_nonneg hrm.roll.1 hrm.roll.2.1 hrm.roll.2.2
  obtain ⟨qf, -⟩ := radians_nonneg hrm.pitch.1 hrm.pitch.2.1 hrm.pitch.2.2
  obtain ⟨yf, -⟩ := radians_nonneg hrm.yaw.1 hrm.yaw.2.1 hrm.yaw.2.2
  have hym : ym.IsFinite := by
    simp only [ym]; split
    · exact hin.slew
    · exact yf
  have H1 : IdQ s1._attitude_target ∧ ZV s1._ang_vel_target_rads ∧
      ZV s1._ang_accel_target_rads ∧ s1._angle_P_scale = s._angle_P_scale ∧ s1._dt_s = s._dt_s ∧
      s1._euler_angle_target_rad = s3._euler_angle_target_rad := by
    simp only [s1]
    split
    · have cx := attitude_command_model_Z C E.1 Z_lit0 hv3.1 ha3.1 rf hin.accr hin.tc hin.dt
        hin.accrb hin.dtb
      have cy := attitude_command_model_Z C E.2.1 Z_lit0 hv3.2.1 ha3.2.1 qf hin.accp hin.tc hin.dt
        hin.accpb hin.dtb
      have cz := attitude_command_model_Z C Z_lit0 hhr hv3.2.2 ha3.2.2 hym hin.accy hin.ytc
        hin.dt hin.accyb hin.dtb
      exact ⟨ht3, ⟨cx.1, cy.1, cz.1⟩, ⟨cx.2, cy.2, cz.2⟩, rfl, rfl, rfl⟩
    · have hr : Z hrr := by
        simp only [hrr]; split
        · rename_i hpos
          have := is_positive_ge hym hpos
          exact constrain_sym_Z hhr hym (by linarith [eps_pos])
        · exact hhr
      have hyq : yq = ⟨1.0, 0.0, 0.0, 0.0⟩ :=
        from_axis_angle_Z ⟨Z_lit0, Z_lit0, Z_mul_left hr hin.dt⟩
      have hat : IdQ at2 := by
        simp only [at2]; rw [E0, hyq]
        exact mul_Id (mul_Id ht3 IdQ_lit) IdQ_lit
      exact ⟨normalize_Id hat, ZV_zero_lit, ZV_zero_lit, rfl, rfl, rfl⟩
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := H1
  have h0t : IdQ s0._attitude_target := h1
  have h0v : ZV s0._ang_vel_target_rads := h2
  have h0e : ZV s0._euler_rate_target_rads :=
    body_to_euler_derivative_Id L h1 h2 s1._euler_rate_target_rads
  have h0a : ZV s0._euler_angle_target_rad := by
    show ZV s1._euler_angle_target_rad
    rw [h6]; exact he3
  have hang0 : AngOK p s0 := by
    have e4 : s0._angle_P_scale = s._angle_P_scale := h4
    have e5 : s0._dt_s = s._dt_s := h5
    exact ⟨hang.kr, hang.kp, hang.ky, hang.krb, hang.kpb, hang.kyb, e4 ▸ hang.sx, e4 ▸ hang.sy,
      e4 ▸ hang.sz, e4 ▸ hang.sxb, e4 ▸ hang.syb, e4 ▸ hang.szb, e5 ▸ hang.dt⟩
  obtain ⟨R1, R2, R3, R4, -, R6, R7, R8, R9, R10⟩ :=
    attitude_controller_run_quat_Z L p get_rate_yaw_pid hcap hrm s0 hang0 h0t h0v hb
  exact ⟨R1, R2 ▸ h0t, R3, R4, R7 ▸ h0v, R8 ▸ (h3 : ZV s0._ang_accel_target_rads), R9 ▸ h0e,
    R10 ▸ h0a, R6⟩

/-- `input_thrust_vector_heading_rad_Z` with two more conclusions: the target Euler angles are
zeros and the feed-forward scalar is `1.0`. Same hypotheses. -/
theorem input_thrust_vector_heading_rad_Z_full (L : LibmZero32) (C : ConvZero)
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
      ZV r._euler_rate_target_rads ∧ ZV r._euler_angle_target_rad ∧
      r._feedforward_scalar = 1.0 := by
  intro r
  unfold r input_thrust_vector_heading_rad
  simp (config := {zeta := false}) only []
  extract_lets s4 s3 dq s2 s1 s0
  have ht3 : IdQ s3._attitude_target := update_attitude_target_Id s ht hv hin.dt
  have he3 : ZV s3._euler_angle_target_rad := to_euler_vec_Id L ht3
  have hv3 : ZV s3._ang_vel_target_rads := hv
  have ha3 : ZV s3._ang_accel_target_rads := ha
  have hdq : IdQ dq := attitude_from_thrust_vector_Id L hx hy hz hh
  obtain ⟨rf, -⟩ := radians_nonneg hrm.roll.1 hrm.roll.2.1 hrm.roll.2.2
  obtain ⟨qf, -⟩ := radians_nonneg hrm.pitch.1 hrm.pitch.2.1 hrm.pitch.2.2
  have H1 : IdQ s1._attitude_target ∧ ZV s1._ang_vel_target_rads ∧
      ZV s1._ang_accel_target_rads ∧ s1._angle_P_scale = s._angle_P_scale ∧ s1._dt_s = s._dt_s ∧
      s1._euler_angle_target_rad = s3._euler_angle_target_rad := by
    simp only [s1]
    split
    · have E := (thrust_vector_rotation_angles_Id L hdq ht3).2.1
      have cx := attitude_command_model_Z C E.1 Z_lit0 hv3.1 ha3.1 rf hin.accr hin.tc hin.dt
        hin.accrb hin.dtb
      have cy := attitude_command_model_Z C E.2.1 Z_lit0 hv3.2.1 ha3.2.1 qf hin.accp hin.tc hin.dt
        hin.accpb hin.dtb
      have cz := attitude_command_model_Z C E.2.2 hhr hv3.2.2 ha3.2.2 hin.slew hin.accy hin.ytc
        hin.dt hin.accyb hin.dtb
      exact ⟨ht3, ⟨cx.1, cy.1, cz.1⟩, ⟨cx.2, cy.2, cz.2⟩, rfl, rfl, rfl⟩
    · exact ⟨hdq, ZV_zero_lit, ZV_zero_lit, rfl, rfl, rfl⟩
  obtain ⟨h1, h2, h3, h4, h5, h6⟩ := H1
  have h0t : IdQ s0._attitude_target := h1
  have h0v : ZV s0._ang_vel_target_rads := h2
  have h0e : ZV s0._euler_rate_target_rads :=
    body_to_euler_derivative_Id L h1 h2 s1._euler_rate_target_rads
  have h0a : ZV s0._euler_angle_target_rad := by
    show ZV s1._euler_angle_target_rad
    rw [h6]; exact he3
  have hang0 : AngOK p s0 := by
    have e4 : s0._angle_P_scale = s._angle_P_scale := h4
    have e5 : s0._dt_s = s._dt_s := h5
    exact ⟨hang.kr, hang.kp, hang.ky, hang.krb, hang.kpb, hang.kyb, e4 ▸ hang.sx, e4 ▸ hang.sy,
      e4 ▸ hang.sz, e4 ▸ hang.sxb, e4 ▸ hang.syb, e4 ▸ hang.szb, e5 ▸ hang.dt⟩
  obtain ⟨R1, R2, R3, R4, -, R6, R7, R8, R9, R10⟩ :=
    attitude_controller_run_quat_Z L p get_rate_yaw_pid hcap hrm s0 hang0 h0t h0v hb
  exact ⟨R1, R2 ▸ h0t, R3, R4, R7 ▸ h0v, R8 ▸ (h3 : ZV s0._ang_accel_target_rads), R9 ▸ h0e,
    R10 ▸ h0a, R6⟩

/-! ## Frames -/

/-- `attitude_controller_run_quat` writes only the target, the thrust angles, the feed-forward
scalar, the recorded error and the body-rate demand. -/
theorem attitude_controller_run_quat_frame (p : AC_AttitudeControl.Params)
    (get_rate_yaw_pid : AC_PID.Params) (s : AC_AttitudeControl.State) (body : Quaternion) :
    attitude_controller_run_quat p get_rate_yaw_pid s body =
      { s with
        _attitude_target :=
          (attitude_controller_run_quat p get_rate_yaw_pid s body)._attitude_target
        _thrust_angle_rad :=
          (attitude_controller_run_quat p get_rate_yaw_pid s body)._thrust_angle_rad
        _thrust_error_angle_rad :=
          (attitude_controller_run_quat p get_rate_yaw_pid s body)._thrust_error_angle_rad
        _feedforward_scalar :=
          (attitude_controller_run_quat p get_rate_yaw_pid s body)._feedforward_scalar
        _attitude_ang_error :=
          (attitude_controller_run_quat p get_rate_yaw_pid s body)._attitude_ang_error
        _ang_vel_body_rads :=
          (attitude_controller_run_quat p get_rate_yaw_pid s body)._ang_vel_body_rads } := by
  unfold attitude_controller_run_quat
  generalize thrust_heading_rotation_angles p get_rate_yaw_pid s._attitude_target body = T
  obtain ⟨c, e, a, d⟩ := T
  simp only []
  split_ifs <;> rfl

/-- `input_thrust_vector_rate_heading_rads` writes only the attitude-controller outputs: the
target, its Euler angles and rates, the target rate and acceleration, the thrust angles, the
feed-forward scalar, the recorded error and the body-rate demand. Every other field (`_dt_s`, the
time constants, the scales, the system-identification offsets, the throttle fields,
`_rate_gyro_rads`, ...) is unchanged. -/
theorem input_thrust_vector_rate_heading_rads_frame (p : AC_AttitudeControl.Params)
    (get_rate_yaw_pid : AC_PID.Params)
    (s : AC_AttitudeControl.State) (body : Quaternion) (tv : Vector3f) (heading_rate : Float32)
    (slew_yaw : Bool) :
    let r := input_thrust_vector_rate_heading_rads p get_rate_yaw_pid s body tv heading_rate
      slew_yaw
    r = { s with
      _euler_angle_target_rad := r._euler_angle_target_rad
      _euler_rate_target_rads := r._euler_rate_target_rads
      _attitude_target := r._attitude_target
      _ang_vel_target_rads := r._ang_vel_target_rads
      _ang_accel_target_rads := r._ang_accel_target_rads
      _ang_vel_body_rads := r._ang_vel_body_rads
      _attitude_ang_error := r._attitude_ang_error
      _thrust_angle_rad := r._thrust_angle_rad
      _thrust_error_angle_rad := r._thrust_error_angle_rad
      _feedforward_scalar := r._feedforward_scalar } := by
  intro r
  simp only [r, input_thrust_vector_rate_heading_rads]
  rw [attitude_controller_run_quat_frame]
  cases p._rate_bf_ff_enabled <;> rfl

/-- `input_thrust_vector_heading_rad` writes the same fields as
`input_thrust_vector_rate_heading_rads` (`input_thrust_vector_rate_heading_rads_frame`) and no
others. -/
theorem input_thrust_vector_heading_rad_frame (p : AC_AttitudeControl.Params)
    (get_rate_yaw_pid : AC_PID.Params)
    (s : AC_AttitudeControl.State) (body : Quaternion) (tv : Vector3f)
    (heading heading_rate : Float32) :
    let r := input_thrust_vector_heading_rad p get_rate_yaw_pid s body tv heading heading_rate
    r = { s with
      _euler_angle_target_rad := r._euler_angle_target_rad
      _euler_rate_target_rads := r._euler_rate_target_rads
      _attitude_target := r._attitude_target
      _ang_vel_target_rads := r._ang_vel_target_rads
      _ang_accel_target_rads := r._ang_accel_target_rads
      _ang_vel_body_rads := r._ang_vel_body_rads
      _attitude_ang_error := r._attitude_ang_error
      _thrust_angle_rad := r._thrust_angle_rad
      _thrust_error_angle_rad := r._thrust_error_angle_rad
      _feedforward_scalar := r._feedforward_scalar } := by
  intro r
  simp only [r, input_thrust_vector_heading_rad]
  rw [attitude_controller_run_quat_frame]
  cases p._rate_bf_ff_enabled <;> rfl

/-! ## The `AC_AttitudeControl_Multi` wrappers -/

/-- `input_thrust_vector_heading` with a `Rate_Only` command is the base-class
`input_thrust_vector_rate_heading_rads` (with `slew_yaw = true`) on `toState`. -/
theorem multi_heading_rate_only (p : AC_AttitudeControl_Multi.Params)
    (s : AC_AttitudeControl_Multi.State) (body : Quaternion) (tv : Vector3f) (h : HeadingCommand)
    (hm : h.heading_mode = .Rate_Only) :
    AC_AttitudeControl_Multi.input_thrust_vector_heading p s body tv h =
      { s with toState := (input_thrust_vector_rate_heading_rads p.toParams
          (AC_AttitudeControl_Multi.get_rate_yaw_pid p) s.toState body tv h.yaw_rate_rads
          true) } := by
  obtain ⟨a, r, m⟩ := h
  simp only at hm
  subst hm
  rfl

/-- `input_thrust_vector_heading` with an `Angle_And_Rate` command is the base-class
`input_thrust_vector_heading_rad` on `toState`. -/
theorem multi_heading_angle_and_rate (p : AC_AttitudeControl_Multi.Params)
    (s : AC_AttitudeControl_Multi.State) (body : Quaternion) (tv : Vector3f) (h : HeadingCommand)
    (hm : h.heading_mode = .Angle_And_Rate) :
    AC_AttitudeControl_Multi.input_thrust_vector_heading p s body tv h =
      { s with toState := (input_thrust_vector_heading_rad p.toParams
          (AC_AttitudeControl_Multi.get_rate_yaw_pid p) s.toState body tv h.yaw_angle_rad
          h.yaw_rate_rads) } := by
  obtain ⟨a, r, m⟩ := h
  simp only at hm
  subst hm
  rfl

/-- **The Multi thrust-vector entry at the hover, `Rate_Only` (AutoYaw `HOLD`).** The result
differs from `s` only in the ten attitude-controller outputs (so the three rate PID states, `_dt_s`,
the time constants, the scales, the system-identification offsets, the throttle fields and
`_rate_gyro_rads` are unchanged), and those outputs are at the hover fixed point. -/
theorem multi_rate_only_Z (L : LibmZero32) (C : ConvZero) (p : AC_AttitudeControl_Multi.Params)
    (hcap : ¬ (yaw_error_cap p.toParams (AC_AttitudeControl_Multi.get_rate_yaw_pid p) < 0))
    (hrm : RateMaxOK p.toParams) (s : AC_AttitudeControl_Multi.State)
    (hang : AngOK p.toParams s.toState) (hin : InputOK p.toParams s.toState)
    (ht : IdQ s._attitude_target) (hv : ZV s._ang_vel_target_rads)
    (ha : ZV s._ang_accel_target_rads) {body : Quaternion} (hb : IdQ body) {tv : Vector3f}
    (hx : Z tv.x) (hy : Z tv.y) (hz : tv.z = -GRAVITY_MSS) (h : HeadingCommand)
    (hm : h.heading_mode = .Rate_Only) (hhr : Z h.yaw_rate_rads) :
    let r := AC_AttitudeControl_Multi.input_thrust_vector_heading p s body tv h
    r = { s with
      _euler_angle_target_rad := r._euler_angle_target_rad
      _euler_rate_target_rads := r._euler_rate_target_rads
      _attitude_target := r._attitude_target
      _ang_vel_target_rads := r._ang_vel_target_rads
      _ang_accel_target_rads := r._ang_accel_target_rads
      _ang_vel_body_rads := r._ang_vel_body_rads
      _attitude_ang_error := r._attitude_ang_error
      _thrust_angle_rad := r._thrust_angle_rad
      _thrust_error_angle_rad := r._thrust_error_angle_rad
      _feedforward_scalar := r._feedforward_scalar } ∧
    ZV r._ang_vel_body_rads ∧ IdQ r._attitude_target ∧ Z r._thrust_angle_rad ∧
      Z r._thrust_error_angle_rad ∧ ZV r._ang_vel_target_rads ∧ ZV r._ang_accel_target_rads ∧
      ZV r._euler_rate_target_rads ∧ ZV r._euler_angle_target_rad ∧
      r._feedforward_scalar = 1.0 := by
  intro r
  have hr : r = _ := multi_heading_rate_only p s body tv h hm
  have hf := input_thrust_vector_rate_heading_rads_frame p.toParams
    (AC_AttitudeControl_Multi.get_rate_yaw_pid p) s.toState
    body tv h.yaw_rate_rads true
  simp only at hf
  refine ⟨?_, ?_⟩
  · rw [hr]; conv_lhs => rw [hf]
  · rw [hr]
    exact input_thrust_vector_rate_heading_rads_Z L C p.toParams _ hcap hrm s.toState hang hin ht
      hv ha hb hx hy hz hhr true

/-- **The Multi thrust-vector entry at the hover, `Angle_And_Rate` (AutoYaw `LOOK_AT_NEXT_WP`)**,
with a zero heading and heading rate: as `multi_rate_only_Z`. -/
theorem multi_angle_and_rate_Z (L : LibmZero32) (C : ConvZero)
    (p : AC_AttitudeControl_Multi.Params)
    (hcap : ¬ (yaw_error_cap p.toParams (AC_AttitudeControl_Multi.get_rate_yaw_pid p) < 0))
    (hrm : RateMaxOK p.toParams) (s : AC_AttitudeControl_Multi.State)
    (hang : AngOK p.toParams s.toState) (hin : InputOK p.toParams s.toState)
    (ht : IdQ s._attitude_target) (hv : ZV s._ang_vel_target_rads)
    (ha : ZV s._ang_accel_target_rads) {body : Quaternion} (hb : IdQ body) {tv : Vector3f}
    (hx : Z tv.x) (hy : Z tv.y) (hz : tv.z = -GRAVITY_MSS) (h : HeadingCommand)
    (hm : h.heading_mode = .Angle_And_Rate) (hh : Z h.yaw_angle_rad) (hhr : Z h.yaw_rate_rads) :
    let r := AC_AttitudeControl_Multi.input_thrust_vector_heading p s body tv h
    r = { s with
      _euler_angle_target_rad := r._euler_angle_target_rad
      _euler_rate_target_rads := r._euler_rate_target_rads
      _attitude_target := r._attitude_target
      _ang_vel_target_rads := r._ang_vel_target_rads
      _ang_accel_target_rads := r._ang_accel_target_rads
      _ang_vel_body_rads := r._ang_vel_body_rads
      _attitude_ang_error := r._attitude_ang_error
      _thrust_angle_rad := r._thrust_angle_rad
      _thrust_error_angle_rad := r._thrust_error_angle_rad
      _feedforward_scalar := r._feedforward_scalar } ∧
    ZV r._ang_vel_body_rads ∧ IdQ r._attitude_target ∧ Z r._thrust_angle_rad ∧
      Z r._thrust_error_angle_rad ∧ ZV r._ang_vel_target_rads ∧ ZV r._ang_accel_target_rads ∧
      ZV r._euler_rate_target_rads ∧ ZV r._euler_angle_target_rad ∧
      r._feedforward_scalar = 1.0 := by
  intro r
  have hr : r = _ := multi_heading_angle_and_rate p s body tv h hm
  have hf := input_thrust_vector_heading_rad_frame p.toParams
    (AC_AttitudeControl_Multi.get_rate_yaw_pid p) s.toState
    body tv h.yaw_angle_rad h.yaw_rate_rads
  simp only at hf
  refine ⟨?_, ?_⟩
  · rw [hr]; conv_lhs => rw [hf]
  · rw [hr]
    exact input_thrust_vector_heading_rad_Z_full L C p.toParams _ hcap hrm s.toState hang hin ht
      hv ha hb hx hy hz hh hhr

/-! ## `AutoYaw.get_heading` -/

/-- **`get_heading` in `HOLD`**: only `auto_yaw` changes (the pilot rate, the yaw angle, the yaw
rate; `_mode` stays), and the command is `Rate_Only` with a `0.0` rate and the target's Euler yaw
as angle. -/
theorem get_heading_hold (s : Copter.State) (h : s.auto_yaw._mode = .HOLD) :
    Copter.AutoYaw.get_heading s =
      ({ s with auto_yaw := { s.auto_yaw with
          _pilot_yaw_rate_rads := 0.0
          _yaw_angle_rad := s.attitude_control._euler_angle_target_rad.z
          _yaw_rate_rads := 0.0 } },
       { yaw_angle_rad := s.attitude_control._euler_angle_target_rad.z, yaw_rate_rads := 0.0,
         heading_mode := .Rate_Only }) := by
  obtain ⟨sc, ah, ig, mo, ac, pc, wn, ay, ma, ia, act⟩ := s
  obtain ⟨m, ya, yr, la, pr⟩ := ay
  simp only at h
  subst h
  rfl

/-- **`get_heading` in `LOOK_AT_NEXT_WP`**: only `auto_yaw` changes, and the command is
`Angle_And_Rate` with the position controller's yaw and yaw rate. -/
theorem get_heading_next_wp (s : Copter.State) (h : s.auto_yaw._mode = .LOOK_AT_NEXT_WP) :
    Copter.AutoYaw.get_heading s =
      ({ s with auto_yaw := { s.auto_yaw with
          _pilot_yaw_rate_rads := 0.0
          _yaw_angle_rad := AC_PosControl.get_yaw_rad s.pos_control
          _yaw_rate_rads := AC_PosControl.get_yaw_rate_rads s.pos_control } },
       { yaw_angle_rad := AC_PosControl.get_yaw_rad s.pos_control,
         yaw_rate_rads := AC_PosControl.get_yaw_rate_rads s.pos_control,
         heading_mode := .Angle_And_Rate }) := by
  obtain ⟨sc, ah, ig, mo, ac, pc, wn, ay, ma, ia, act⟩ := s
  obtain ⟨m, ya, yr, la, pr⟩ := ay
  simp only at h
  subst h
  rfl

/-! ## The run parameters -/

/-- The literal `1000.0`. -/
theorem lit_thousand : (1000.0 : Float32).IsFinite ∧ (1000.0 : Float32).toReal = 1000 := by
  obtain ⟨h1, h2⟩ := litPos (x := (1000.0 : Float32)) (m := 16384000) (e := -14)
    (hm := by decide) rfl
  exact ⟨h1, by rw [h2]; norm_num⟩

/-- A finite float between the literals `-1000.0` and `1000.0` is at most `1000` in magnitude (the
comparisons are decided by the kernel on concrete floats). -/
theorem abs_le_thousand {x : Float32} (hx : x.IsFinite) (h1 : x ≤ 1000.0) (h2 : -1000.0 ≤ x) :
    |x.toReal| ≤ 1000 := by
  have hn : (-1000.0 : Float32).IsFinite := (Float32.isFinite_neg _).2 lit_thousand.1
  rw [le_iff hx lit_thousand.1, lit_thousand.2] at h1
  rw [le_iff hn hx, Float32.toReal_neg, lit_thousand.2] at h2
  exact abs_le.2 ⟨h2, h1⟩

/-- A finite float with `0 ≤ x` (as floats) is non-negative in value. -/
theorem nonneg_of_le {x : Float32} (hx : x.IsFinite) (h : (0 : Float32) ≤ x) : 0 ≤ x.toReal := by
  rw [le_iff Float32.isFinite_zero hx, Float32.toReal_zero] at h; exact h

/-- `PidOK` from kernel-decidable facts about the gains. -/
theorem pidOK_of (p : AC_PID.Params) (hP : p.P.IsFinite) (hI : p.I.IsFinite) (hD : p.D.IsFinite)
    (hFF : p.FF.IsFinite) (hIM : p.IMAX.IsFinite) (hIM0 : (0 : Float32) ≤ p.IMAX)
    (hPD : p.PDMX.IsFinite) (hDF : p.D_FF.IsFinite) (hT : p.FLTT.IsFinite) (hE : p.FLTE.IsFinite)
    (hDD : p.FLTD.IsFinite) (hT1 : p.FLTT ≤ 1000.0) (hT2 : -1000.0 ≤ p.FLTT)
    (hE1 : p.FLTE ≤ 1000.0) (hE2 : -1000.0 ≤ p.FLTE) (hD1 : p.FLTD ≤ 1000.0)
    (hD2 : -1000.0 ≤ p.FLTD) : PidOK p :=
  ⟨hP, hI, hD, hFF, hIM, nonneg_of_le hIM hIM0, hPD, hDF, hT, hE, hDD,
    (abs_le_thousand hT hT1 hT2).trans (by norm_num),
    (abs_le_thousand hE hE1 hE2).trans (by norm_num),
    (abs_le_thousand hDD hD1 hD2).trans (by norm_num)⟩

/-- The rate PID gains of the run parameters are `PidOK`. -/
theorem runParams_ratePidsOK : RatePidsOK runParams.att :=
  ⟨pidOK_of _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide),
    pidOK_of _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide),
    pidOK_of _ (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide)⟩

/-- A rate limit from kernel-decidable comparisons with `0` and `1000.0`. -/
theorem rateMax_of {x : Float32} (hx : x.IsFinite) (h0 : (0 : Float32) ≤ x) (h1 : x ≤ 1000.0) :
    x.IsFinite ∧ 0 ≤ x.toReal ∧ x.toReal ≤ 1e30 := by
  refine ⟨hx, nonneg_of_le hx h0, ?_⟩
  rw [le_iff hx lit_thousand.1, lit_thousand.2] at h1
  linarith

/-- The rate limits of the run parameters (`ATC_RATE_R/P/Y_MAX = 0`, unlimited). -/
theorem runParams_rateMaxOK : RateMaxOK runParams.att.toParams :=
  ⟨rateMax_of (by decide) (by decide) (by decide), rateMax_of (by decide) (by decide) (by decide),
    rateMax_of (by decide) (by decide) (by decide)⟩

set_option maxRecDepth 10000 in
/-- The yaw-error cap of the run parameters is not negative (it is `radians(45)`). -/
theorem runParams_cap :
    ¬ (yaw_error_cap runParams.att.toParams
      (AC_AttitudeControl_Multi.get_rate_yaw_pid runParams.att) < 0) := by
  decide

/-- `|dtF| ≤ 10¹⁸`. -/
theorem dtF_abs : |dtF.toReal| ≤ 1e18 := by
  rw [dtF_val.2, CopterVert.dtc]; norm_num

/-- `InputOK` for the run parameters, at the loop time `dtF` and the rate time constant
`PILOT_Y_RATE_TC` set on entering Auto. -/
theorem runParams_inputOK (s : AC_AttitudeControl.State) (hdt : s._dt_s = dtF)
    (hy : s._rate_y_tc = runParams.PILOT_Y_RATE_TC) : InputOK runParams.att.toParams s := by
  refine ⟨by decide, by decide, by decide, abs_le_thousand (by decide) (by decide) (by decide),
    abs_le_thousand (by decide) (by decide) (by decide),
    abs_le_thousand (by decide) (by decide) (by decide), by decide, ?_, by decide, ?_, ?_⟩
  · rw [hy]; decide
  · rw [hdt]; exact dtF_val.1
  · rw [hdt]; exact dtF_abs

/-- `AngOK` for the run parameters, at the loop time `dtF` and the unit angle-P scale. -/
theorem runParams_angOK (s : AC_AttitudeControl.State) (hdt : s._dt_s = dtF)
    (hP : s._angle_P_scale = VECTORF_111) : AngOK runParams.att.toParams s := by
  have h1 : |(1.0 : Float32).toReal| ≤ 1e9 := by rw [lit_one.2]; norm_num
  have k : ∀ x : Float32, x.IsFinite → x ≤ 1000.0 → -1000.0 ≤ x → |x.toReal| ≤ 1e9 :=
    fun x hx a b => (abs_le_thousand hx a b).trans (by norm_num)
  have ex : s._angle_P_scale.x = 1.0 := by rw [hP]; rfl
  have ey : s._angle_P_scale.y = 1.0 := by rw [hP]; rfl
  have ez : s._angle_P_scale.z = 1.0 := by rw [hP]; rfl
  refine ⟨by decide, by decide, by decide, k _ (by decide) (by decide) (by decide),
    k _ (by decide) (by decide) (by decide), k _ (by decide) (by decide) (by decide),
    ex ▸ lit_one.1, ey ▸ lit_one.1, ez ▸ lit_one.1, ex ▸ h1, ey ▸ h1, ez ▸ h1, ?_⟩
  rw [hdt]; exact dtF_val.1

/-! ## The rate-controller stage -/

/-- With the throttle slew rate `0.0` the gain boost is the identity (`0 > 1` is false). -/
theorem gain_boost_zero (p : AC_AttitudeControl_Multi.Params) (s : AC_AttitudeControl_Multi.State) :
    AC_AttitudeControl_Multi.update_throttle_gain_boost p s 0.0 = s := by
  unfold AC_AttitudeControl_Multi.update_throttle_gain_boost
  rw [if_neg (by decide)]

/-- `rate_controller_run_dt` with slew rate `0.0` writes, in the attitude state, only the gyro,
`_throttle_rpy_mix`, the three rate PIDs and the three `_used` scales (the latter copies of the
current scales); in the motors record, only the six roll, pitch, yaw inputs. -/
theorem rate_controller_run_dt_frame (p : AC_AttitudeControl_Multi.Params)
    (s : AC_AttitudeControl_Multi.State) (m : AP_Motors.Inputs) (gyro : Vector3f) (dt : Float32) :
    let R := AC_AttitudeControl_Multi.rate_controller_run_dt p s m 0.0 gyro dt
    R.1 = { s with
      _rate_gyro_rads := gyro
      _throttle_rpy_mix := R.1._throttle_rpy_mix
      _pid_rate_roll := R.1._pid_rate_roll
      _pid_rate_pitch := R.1._pid_rate_pitch
      _pid_rate_yaw := R.1._pid_rate_yaw
      _pd_scale_used := s._pd_scale
      _i_scale_used := s._i_scale
      _angle_P_scale_used := s._angle_P_scale } ∧
    R.2 = { m with
      _roll_in := R.2._roll_in
      _pitch_in := R.2._pitch_in
      _yaw_in := R.2._yaw_in
      _roll_in_ff := R.2._roll_in_ff
      _pitch_in_ff := R.2._pitch_in_ff
      _yaw_in_ff := R.2._yaw_in_ff } := by
  intro R
  simp only [R, AC_AttitudeControl_Multi.rate_controller_run_dt, gain_boost_zero]
  exact ⟨rfl, rfl⟩

/-- The rate-controller stage for any parameters with `RatePidsOK` and any finite loop time `dt`
of magnitude at most `10³⁰` (`run_rate_controller_main_Z` is the instance at `runParams`, `dtF`).
Stated generally so that the loop time and the gains stay symbolic in the proof. -/
theorem run_rate_controller_main_gen (P : Copter.Parameters) (hP : RatePidsOK P.att)
    (s : Copter.State) {dt : Float32} (hdt : s.scheduler.last_loop_time_s = dt)
    (hdtf : dt.IsFinite) (hdtb : |dt.toReal| ≤ 1e30)
    (hg : ZV s.ins_gyro) (hbody : ZV s.attitude_control._ang_vel_body_rads)
    (hsys : ZV s.attitude_control._sysid_ang_vel_body_rads)
    (hact : ZV s.attitude_control._actuator_sysid) (hr : ZPID s.attitude_control._pid_rate_roll)
    (hq : ZPID s.attitude_control._pid_rate_pitch) (hy : ZPID s.attitude_control._pid_rate_yaw)
    (hpd : s.attitude_control._pd_scale = VECTORF_111)
    (hi : s.attitude_control._i_scale = VECTORF_111)
    (hff : s.attitude_control._feedforward_scalar.IsFinite) :
    ∃ (mix : Float32) (pr pp py : AC_PID.State) (r1 r2 r3 f1 f2 f3 : Float32),
      ZPID pr ∧ ZPID pp ∧ ZPID py ∧ Z r1 ∧ Z r2 ∧ Z r3 ∧ Z f1 ∧ Z f2 ∧ Z f3 ∧
      Copter.run_rate_controller_main P s =
        { s with
          pos_control := AC_PosControl.set_dt_s s.pos_control dt
          attitude_control := { s.attitude_control with
            _dt_s := dt
            _rate_gyro_rads := s.ins_gyro
            _throttle_rpy_mix := mix
            _pid_rate_roll := pr
            _pid_rate_pitch := pp
            _pid_rate_yaw := py
            _pd_scale_used := s.attitude_control._pd_scale
            _i_scale_used := s.attitude_control._i_scale
            _angle_P_scale_used := s.attitude_control._angle_P_scale
            _sysid_ang_vel_body_rads := ⟨0, 0, 0⟩
            _actuator_sysid := ⟨0, 0, 0⟩
            _pd_scale := VECTORF_111
            _i_scale := VECTORF_111
            _angle_P_scale := VECTORF_111 }
          motors := { s.motors with
            _dt_s := dt
            _roll_in := r1
            _pitch_in := r2
            _yaw_in := r3
            _roll_in_ff := f1
            _pitch_in_ff := f2
            _yaw_in_ff := f3 } } := by
  subst hdt
  have px : s.attitude_control._pd_scale.x = 1.0 := by rw [hpd]; rfl
  have py' : s.attitude_control._pd_scale.y = 1.0 := by rw [hpd]; rfl
  have pz : s.attitude_control._pd_scale.z = 1.0 := by rw [hpd]; rfl
  have ix : s.attitude_control._i_scale.x = 1.0 := by rw [hi]; rfl
  have iy : s.attitude_control._i_scale.y = 1.0 := by rw [hi]; rfl
  have iz : s.attitude_control._i_scale.z = 1.0 := by rw [hi]; rfl
  have h1 : |(1.0 : Float32).toReal| ≤ 1e30 := by rw [lit_one.2]; norm_num
  obtain ⟨Z1, Z2, Z3, Z4, Z5, Z6, P1, P2, P3, -⟩ :=
    rate_controller_run_dt_Z P.att hP
      (AC_AttitudeControl_Multi.set_dt_s s.attitude_control s.scheduler.last_loop_time_s)
      hbody hsys hact hr hq hy ⟨px ▸ lit_one.1, py' ▸ lit_one.1, pz ▸ lit_one.1⟩
      ⟨px ▸ h1, py' ▸ h1⟩ ⟨ix ▸ lit_one.1, iy ▸ lit_one.1, iz ▸ lit_one.1⟩ hff
      (AP_MotorsMatrix.set_dt_s s.motors s.scheduler.last_loop_time_s).toInputs 0.0 hg hdtf hdtb
  obtain ⟨F1, F2⟩ := rate_controller_run_dt_frame P.att
    (AC_AttitudeControl_Multi.set_dt_s s.attitude_control s.scheduler.last_loop_time_s)
    (AP_MotorsMatrix.set_dt_s s.motors s.scheduler.last_loop_time_s).toInputs s.ins_gyro
    s.scheduler.last_loop_time_s
  have e : Copter.run_rate_controller_main P s =
      match AC_AttitudeControl_Multi.rate_controller_run_dt P.att
        (AC_AttitudeControl_Multi.set_dt_s s.attitude_control s.scheduler.last_loop_time_s)
        (AP_MotorsMatrix.set_dt_s s.motors s.scheduler.last_loop_time_s).toInputs 0.0 s.ins_gyro
        s.scheduler.last_loop_time_s with
      | (a, m) =>
        { s with pos_control := AC_PosControl.set_dt_s s.pos_control s.scheduler.last_loop_time_s,
                 attitude_control := AC_AttitudeControl_Multi.rate_controller_target_reset a,
                 motors := { AP_MotorsMatrix.set_dt_s s.motors s.scheduler.last_loop_time_s with
                   toInputs := m } } := rfl
  rw [e]
  generalize AC_AttitudeControl_Multi.rate_controller_run_dt P.att
    (AC_AttitudeControl_Multi.set_dt_s s.attitude_control s.scheduler.last_loop_time_s)
    (AP_MotorsMatrix.set_dt_s s.motors s.scheduler.last_loop_time_s).toInputs 0.0 s.ins_gyro
    s.scheduler.last_loop_time_s = R at F1 F2 Z1 Z2 Z3 Z4 Z5 Z6 P1 P2 P3
  obtain ⟨a, m⟩ := R
  simp only at F1 F2 Z1 Z2 Z3 Z4 Z5 Z6 P1 P2 P3
  refine ⟨a._throttle_rpy_mix, a._pid_rate_roll, a._pid_rate_pitch, a._pid_rate_yaw,
    m._roll_in, m._pitch_in, m._yaw_in, m._roll_in_ff, m._pitch_in_ff, m._yaw_in_ff,
    P1, P2, P3, Z1, Z2, Z3, Z4, Z5, Z6, ?_⟩
  rw [F1, F2]
  rfl

/-- **The rate-controller stage `run_rate_controller_main` at the hover**, with the run parameters
and the loop time `dtF`. With a zero gyro, a zero body-rate target, zero system-identification
offsets, the rate PIDs at zero, unit PD and I scales and a finite feed-forward scalar: the stage
sets `dtF` in the position controller, the attitude controller and the motors, writes zeros into
the six roll, pitch, yaw motor inputs (no other motors field changes), keeps the rate PIDs at zero,
stores the gyro, and `rate_controller_target_reset` restores the zero offsets and the unit scales.
Besides those, the attitude state changes only in `_throttle_rpy_mix` and the three `_used` scales
(copies of the scales before the reset). -/
theorem run_rate_controller_main_Z (s : Copter.State) (hdt : s.scheduler.last_loop_time_s = dtF)
    (hg : ZV s.ins_gyro) (hbody : ZV s.attitude_control._ang_vel_body_rads)
    (hsys : ZV s.attitude_control._sysid_ang_vel_body_rads)
    (hact : ZV s.attitude_control._actuator_sysid) (hr : ZPID s.attitude_control._pid_rate_roll)
    (hq : ZPID s.attitude_control._pid_rate_pitch) (hy : ZPID s.attitude_control._pid_rate_yaw)
    (hpd : s.attitude_control._pd_scale = VECTORF_111)
    (hi : s.attitude_control._i_scale = VECTORF_111)
    (hff : s.attitude_control._feedforward_scalar.IsFinite) :
    ∃ (mix : Float32) (pr pp py : AC_PID.State) (r1 r2 r3 f1 f2 f3 : Float32),
      ZPID pr ∧ ZPID pp ∧ ZPID py ∧ Z r1 ∧ Z r2 ∧ Z r3 ∧ Z f1 ∧ Z f2 ∧ Z f3 ∧
      Copter.run_rate_controller_main runParams s =
        { s with
          pos_control := AC_PosControl.set_dt_s s.pos_control dtF
          attitude_control := { s.attitude_control with
            _dt_s := dtF
            _rate_gyro_rads := s.ins_gyro
            _throttle_rpy_mix := mix
            _pid_rate_roll := pr
            _pid_rate_pitch := pp
            _pid_rate_yaw := py
            _pd_scale_used := s.attitude_control._pd_scale
            _i_scale_used := s.attitude_control._i_scale
            _angle_P_scale_used := s.attitude_control._angle_P_scale
            _sysid_ang_vel_body_rads := ⟨0, 0, 0⟩
            _actuator_sysid := ⟨0, 0, 0⟩
            _pd_scale := VECTORF_111
            _i_scale := VECTORF_111
            _angle_P_scale := VECTORF_111 }
          motors := { s.motors with
            _dt_s := dtF
            _roll_in := r1
            _pitch_in := r2
            _yaw_in := r3
            _roll_in_ff := f1
            _pitch_in_ff := f2
            _yaw_in_ff := f3 } } :=
  run_rate_controller_main_gen runParams runParams_ratePidsOK s hdt dtF_val.1
    (dtF_abs.trans (by norm_num)) hg hbody hsys hact hr hq hy hpd hi hff

end Contracts.CopterHover
