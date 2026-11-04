import Contracts.CopterZeroMath

/-!
# Zero lemmas for `AC_AttitudeControl`

At the hover sample the thrust vector is `(±0, ±0, -GRAVITY_MSS)`, the heading is a zero, and the
body and target attitudes are the identity. Then:

- `attitude_from_thrust_vector_Id`: the desired attitude is the identity. The normalised thrust
  vector is `(±0, ±0, -1)` exactly: `sqrtf(fl(g²)) = g` and `-g / g = -1` in binary32 (computed by
  the kernel, `sqrt_sq_GRAVITY`, `neg_g_div_g`), so `up · T = 1`, `acosf(1) = +0` (libm), and both
  `from_axis_angle(axis, θ)` calls take the `is_zero(θ)` branch;
- `thrust_vector_rotation_angles_Id`, `thrust_heading_rotation_angles_Id`: identity against identity
  gives zero errors, zero thrust angles, and leaves the target;
- `update_ang_vel_target_from_att_error_Z`, `ang_vel_limit_Z`: a zero error gives zero rates;
- `attitude_controller_run_quat_Z`: identity body, identity target, zero target rate give a zero
  `_ang_vel_body_rads`, keep the target, record the identity error, zero thrust angles.
-/

open Float.Model UnpackedFloat AP_Math AC_AttitudeControl

namespace Contracts.CopterZero

theorem hmod_v (a b : Vector3f) : a % b = Vector3f.cross a b := rfl
theorem hmul_vv (a b : Vector3f) : a * b = Vector3f.dot a b := rfl
theorem hdiv_v (a : Vector3f) (k : Float32) : a / k = Vector3f.div a k := rfl
theorem hmul_vs (a : Vector3f) (k : Float32) : a * k = Vector3f.mul a k := rfl
theorem hadd_v (a b : Vector3f) : a + b = Vector3f.add a b := rfl

/-! ## Constants -/

theorem lit_neg_one' : (-1.0 : Float32).IsFinite ∧ (-1.0 : Float32).toReal = -1 := lit_neg_one

theorem thrust_err_spec : AC_ATTITUDE_THRUST_ERROR_ANGLE_RAD.IsFinite ∧
    0 < AC_ATTITUDE_THRUST_ERROR_ANGLE_RAD.toReal := by
  obtain ⟨h1, h2⟩ := litPos (x := AC_ATTITUDE_THRUST_ERROR_ANGLE_RAD) (m := 8784530) (e := -24)
    (hm := by decide) (by rfl)
  exact ⟨h1, by rw [h2]; positivity⟩

theorem thrust_err2_spec : (AC_ATTITUDE_THRUST_ERROR_ANGLE_RAD * 2.0).IsFinite ∧
    0 < (AC_ATTITUDE_THRUST_ERROR_ANGLE_RAD * 2.0).toReal := by
  obtain ⟨h1, h2⟩ := litPos (x := AC_ATTITUDE_THRUST_ERROR_ANGLE_RAD * 2.0) (m := 8784530)
    (e := -23) (hm := by decide) (by rfl)
  exact ⟨h1, by rw [h2]; positivity⟩

theorem rp_min_spec : AC_ATTITUDE_ACCEL_RP_CONTROLLER_MIN_RADSS.IsFinite ∧
    0 < AC_ATTITUDE_ACCEL_RP_CONTROLLER_MIN_RADSS.toReal ∧
    AC_ATTITUDE_ACCEL_RP_CONTROLLER_MIN_RADSS.toReal < 1 := by
  obtain ⟨h1, h2⟩ := litPos (x := AC_ATTITUDE_ACCEL_RP_CONTROLLER_MIN_RADSS) (m := 11712706)
    (e := -24) (hm := by decide) (by rfl)
  refine ⟨h1, ?_, ?_⟩ <;> rw [h2] <;> norm_num

theorem rp_max_spec : AC_ATTITUDE_ACCEL_RP_CONTROLLER_MAX_RADSS.IsFinite ∧
    1 < AC_ATTITUDE_ACCEL_RP_CONTROLLER_MAX_RADSS.toReal ∧
    AC_ATTITUDE_ACCEL_RP_CONTROLLER_MAX_RADSS.toReal < 13 := by
  obtain ⟨h1, h2⟩ := litPos (x := AC_ATTITUDE_ACCEL_RP_CONTROLLER_MAX_RADSS) (m := 13176795)
    (e := -20) (hm := by decide) (by rfl)
  refine ⟨h1, ?_, ?_⟩ <;> rw [h2] <;> norm_num

theorem y_min_spec : AC_ATTITUDE_ACCEL_Y_CONTROLLER_MIN_RADSS.IsFinite ∧
    0 < AC_ATTITUDE_ACCEL_Y_CONTROLLER_MIN_RADSS.toReal ∧
    AC_ATTITUDE_ACCEL_Y_CONTROLLER_MIN_RADSS.toReal < 1 := by
  obtain ⟨h1, h2⟩ := litPos (x := AC_ATTITUDE_ACCEL_Y_CONTROLLER_MIN_RADSS) (m := 11712706)
    (e := -26) (hm := by decide) (by rfl)
  refine ⟨h1, ?_, ?_⟩ <;> rw [h2] <;> norm_num

theorem y_max_spec : AC_ATTITUDE_ACCEL_Y_CONTROLLER_MAX_RADSS.IsFinite ∧
    1 < AC_ATTITUDE_ACCEL_Y_CONTROLLER_MAX_RADSS.toReal ∧
    AC_ATTITUDE_ACCEL_Y_CONTROLLER_MAX_RADSS.toReal < 13 := by
  obtain ⟨h1, h2⟩ := litPos (x := AC_ATTITUDE_ACCEL_Y_CONTROLLER_MAX_RADSS) (m := 8784530)
    (e := -22) (hm := by decide) (by rfl)
  refine ⟨h1, ?_, ?_⟩ <;> rw [h2] <;> norm_num

/-- `constrain_float x lo hi` with literal bounds `0 < lo < 1 < hi < 13` is finite and at most `13`
in magnitude, for every `x` (NaN goes to the midpoint). -/
theorem constrain_lits {lo hi : Float32} (hlo : lo.IsFinite ∧ 0 < lo.toReal ∧ lo.toReal < 1)
    (hhi : hi.IsFinite ∧ 1 < hi.toReal ∧ hi.toReal < 13) (x : Float32) :
    (constrain_float x lo hi).IsFinite ∧ |(constrain_float x lo hi).toReal| ≤ 13 := by
  rw [constrain_float_eq]
  have hsum : |lo.toReal + hi.toReal| ≤ maxFinite32 := by
    have := maxFinite32_ge
    rw [abs_le]; constructor <;> linarith
  obtain ⟨h1, h2, h3⟩ := Contracts.Float32Clip.constrain_float_spec hlo.1 hhi.1 (by linarith) hsum x
  exact ⟨h1, by rw [abs_le]; constructor <;> linarith⟩

theorem mul_abs_le {a b : Float32} (ha : a.IsFinite) (hb : b.IsFinite)
    (h : |a.toReal * b.toReal| ≤ 1e38) :
    (a * b).IsFinite ∧ |(a * b).toReal| ≤ 2 * |a.toReal * b.toReal| + 1 := by
  obtain ⟨hf, he⟩ := Float32.mul_err_all ha hb (h.trans maxFinite32_ge)
  have h24 : (2 : ℝ) ^ (-24 : ℤ) ≤ 1 := zpow_le_one_of_nonpos₀ one_le_two (by norm_num)
  have h150 : (2 : ℝ) ^ (-150 : ℤ) ≤ 1 := zpow_le_one_of_nonpos₀ one_le_two (by norm_num)
  have hm : (2 : ℝ) ^ (-24 : ℤ) * |a.toReal * b.toReal| ≤ 1 * |a.toReal * b.toReal| :=
    mul_le_mul_of_nonneg_right h24 (abs_nonneg _)
  have := abs_sub_abs_le_abs_sub (a * b).toReal (a.toReal * b.toReal)
  exact ⟨hf, by linarith⟩

/-! ## The thrust vector `(±0, ±0, -g)` normalised -/

theorem sq_g_ne_zero : ∀ s, (AP_Math.sq (-GRAVITY_MSS)).toModel.unpack ≠ .zero s := by
  intro s h
  rw [show AP_Math.sq (-GRAVITY_MSS) = (-GRAVITY_MSS) * (-GRAVITY_MSS) from rfl,
    sq_GRAVITY_unpack] at h
  cases h

/-- `‖(±0, ±0, -g)‖` is `GRAVITY_MSS`, bit for bit. -/
theorem length_g_unpack {x y : Float32} (hx : Z x) (hy : Z y) :
    (Vector3f.length ⟨x, y, -GRAVITY_MSS⟩).toModel.unpack = GRAVITY_MSS.toModel.unpack := by
  show (Float32.sqrt (AP_Math.sq x + AP_Math.sq y + AP_Math.sq (-GRAVITY_MSS))).toModel.unpack = _
  rw [congr_sqrt (add_unpack_of_Z_left (Z_add (Z_sq hx) (Z_sq hy)) sq_g_ne_zero)]
  exact sqrt_sq_GRAVITY

/-- `(±0, ±0, -g).normalize` is `(±0, ±0, -1)`. -/
theorem normalize_g {x y : Float32} (hx : Z x) (hy : Z y) :
    Z (Vector3f.normalize ⟨x, y, -GRAVITY_MSS⟩).x ∧ Z (Vector3f.normalize ⟨x, y, -GRAVITY_MSS⟩).y ∧
      ((Vector3f.normalize ⟨x, y, -GRAVITY_MSS⟩).z.IsFinite ∧
        (Vector3f.normalize ⟨x, y, -GRAVITY_MSS⟩).z.toReal = -1) := by
  have hl := length_g_unpack hx hy
  obtain ⟨hlf, hlv⟩ := fin_toReal_of_unpack hl
  obtain ⟨hgf, hg1, -⟩ := GRAVITY_MSS_spec
  have hLf : (Vector3f.length ⟨x, y, -GRAVITY_MSS⟩).IsFinite := hlf.2 hgf
  have hL0 : (Vector3f.length ⟨x, y, -GRAVITY_MSS⟩).toReal ≠ 0 := by rw [hlv]; linarith
  refine ⟨Z_div hx hLf hL0, Z_div hy hLf hL0, ?_⟩
  show ((-GRAVITY_MSS) / Vector3f.length ⟨x, y, -GRAVITY_MSS⟩).IsFinite ∧
    ((-GRAVITY_MSS) / Vector3f.length ⟨x, y, -GRAVITY_MSS⟩).toReal = -1
  have hd := (congr_div (a := -GRAVITY_MSS) (c := -GRAVITY_MSS) rfl hl).trans neg_g_div_g
  obtain ⟨hdf, hdv⟩ := fin_toReal_of_unpack hd
  exact ⟨hdf.2 lit_neg_one.1, hdv.trans lit_neg_one.2⟩

/-- `up · n = 1` for `up = (0, 0, -1)` and `n = (±0, ±0, -1)`. -/
theorem dot_up_One {n : Vector3f} (hx : Z n.x) (hy : Z n.y) (hz : n.z.IsFinite ∧ n.z.toReal = -1) :
    One ((⟨0.0, 0.0, -1.0⟩ : Vector3f) * n) := by
  rw [hmul_vv]; unfold Vector3f.dot; simp only []
  have h3' := mul_exact lit_neg_one.1 hz.1 lit_one.1 (by rw [lit_neg_one.2, hz.2, lit_one.2]; norm_num)
  have h3 : One ((-1.0 : Float32) * n.z) := ⟨h3'.1, h3'.2.trans lit_one.2⟩
  exact Z_add_One (Z_add (Z_mul_left Z_lit0 hx.1) (Z_mul_left Z_lit0 hy.1)) h3

/-- `a · b = 1` for `a, b = (±0, ±0, -1)`. -/
theorem dot_down_One {a b : Vector3f} (ha : Z a.x ∧ Z a.y ∧ a.z.IsFinite ∧ a.z.toReal = -1)
    (hb : Z b.x ∧ Z b.y ∧ b.z.IsFinite ∧ b.z.toReal = -1) : One (a * b) := by
  rw [hmul_vv]; unfold Vector3f.dot
  have h3' := mul_exact ha.2.2.1 hb.2.2.1 lit_one.1 (by rw [ha.2.2.2, hb.2.2.2, lit_one.2]; norm_num)
  have h3 : One (a.z * b.z) := ⟨h3'.1, h3'.2.trans lit_one.2⟩
  exact Z_add_One (Z_add (Z_mul_left ha.1 hb.1.1) (Z_mul_left ha.2.1 hb.2.1.1)) h3

/-- `constrain_float(1, -1, 1)` is `1`. -/
theorem constrain_One {x : Float32} (hx : One x) : One (constrain_float x (-1.0) 1.0) := by
  have := constrain_above hx.1 lit_neg_one.1 lit_one.1 (by rw [lit_neg_one.2, lit_one.2]; norm_num)
    (by rw [lit_one.2, hx.2])
  exact ⟨this.1, this.2.trans lit_one.2⟩

/-- **The desired attitude at hover is the identity.** For a thrust vector `(±0, ±0, -g)` and a
zero heading, `attitude_from_thrust_vector` is the Hamilton product of two identity literals. Uses
`acosf(1) = +0`. -/
theorem attitude_from_thrust_vector_Id (L : LibmZero32) {tv : Vector3f} (hx : Z tv.x)
    (hy : Z tv.y) (hz : tv.z = -GRAVITY_MSS) {heading : Float32} (hh : Z heading) :
    IdQ (attitude_from_thrust_vector tv heading) := by
  obtain ⟨x, y, z⟩ := tv
  simp only at hx hy hz
  subst hz
  -- the squared length is not `is_zero`
  obtain ⟨hcf, hcv⟩ := litPos sq_GRAVITY_unpack
  have hls := add_Z_left (Z_add (Z_mul_left hx hx.1) (Z_mul_left hy hy.1)) hcf
  have hnz : is_zero (Vector3f.length_squared ⟨x, y, -GRAVITY_MSS⟩) = false := by
    show is_zero (x * x + y * y + (-GRAVITY_MSS) * (-GRAVITY_MSS)) = false
    refine is_zero_false hls.1 ?_
    rw [hls.2, hcv, eps_eq, abs_of_pos (by positivity)]
    norm_num
  obtain ⟨nx, ny, nz⟩ := normalize_g hx hy
  unfold attitude_from_thrust_vector
  simp only [hnz, Bool.false_eq_true, if_false]
  generalize Vector3f.normalize ⟨x, y, -GRAVITY_MSS⟩ = n at nx ny nz ⊢
  have hang : Z (Float32.acos (constrain_float ((⟨0.0, 0.0, -1.0⟩ : Vector3f) * n) (-1.0) 1.0)) :=
    L.acos_one _ (constrain_One (dot_up_One nx ny nz))
  rw [from_axis_angle_theta_Z _ hang, from_axis_angle_theta_Z _ hh]
  exact mul_Id IdQ_lit IdQ_lit

/-! ## Thrust-vector and heading errors between two identities -/

theorem up_fin : FinV (⟨0.0, 0.0, -1.0⟩ : Vector3f) := ⟨Z_lit0.1, Z_lit0.1, lit_neg_one.1⟩

/-- The thrust direction of the identity: `q * (0, 0, -1) = (±0, ±0, -1)`. -/
theorem rot_up_Id {q : Quaternion} (hq : IdQ q) :
    Z (q * (⟨0.0, 0.0, -1.0⟩ : Vector3f)).x ∧ Z (q * (⟨0.0, 0.0, -1.0⟩ : Vector3f)).y ∧
      (q * (⟨0.0, 0.0, -1.0⟩ : Vector3f)).z.IsFinite ∧
        (q * (⟨0.0, 0.0, -1.0⟩ : Vector3f)).z.toReal = -1 := by
  obtain ⟨h1, h2, h3⟩ := mul_vec_Id hq up_fin
  exact ⟨Z_of_eq h1 Z_lit0, Z_of_eq h2 Z_lit0, h3.1, h3.2.trans lit_neg_one.2⟩

/-- **`thrust_vector_rotation_angles` of identity against identity**: the correction is the identity
literal, the attitude error is zero, the thrust angle and the thrust error angle are zeros. Uses
`acosf(1) = +0` twice. -/
theorem thrust_vector_rotation_angles_Id (L : LibmZero32) {target body : Quaternion}
    (ht : IdQ target) (hb : IdQ body) :
    (thrust_vector_rotation_angles target body).1 = ⟨1.0, 0.0, 0.0, 0.0⟩ ∧
      ZV (thrust_vector_rotation_angles target body).2.1 ∧
      Z (thrust_vector_rotation_angles target body).2.2.1 ∧
      Z (thrust_vector_rotation_angles target body).2.2.2 := by
  have hT := rot_up_Id ht
  have hB := rot_up_Id hb
  unfold thrust_vector_rotation_angles
  simp only []
  generalize target * (⟨0.0, 0.0, -1.0⟩ : Vector3f) = vt at hT ⊢
  generalize body * (⟨0.0, 0.0, -1.0⟩ : Vector3f) = vb at hB ⊢
  have hta : Z (Float32.acos (constrain_float ((⟨0.0, 0.0, -1.0⟩ : Vector3f) * vb) (-1.0) 1.0)) :=
    L.acos_one _ (constrain_One (dot_up_One hB.1 hB.2.1 hB.2.2))
  have hte : Z (Float32.acos (constrain_float (vb * vt) (-1.0) 1.0)) :=
    L.acos_one _ (constrain_One (dot_down_One hB hT))
  rw [from_axis_angle_theta_Z _ hte]
  have hc := to_axis_angle_Id IdQ_lit
  have hh := to_axis_angle_Id (mul_Id (mul_Id (inverse_Id IdQ_lit) (inverse_Id hb)) ht)
  exact ⟨rfl, ⟨hc.1, hc.2.1, hh.2.2⟩, hta, hte⟩

/-- The yaw-error cap of `thrust_heading_rotation_angles` (`AC_AttitudeControl.cpp:1043-1045`), a
function of the parameters only. -/
def yaw_error_cap (p : AC_AttitudeControl.Params) (get_rate_yaw_pid : AC_PID.Params) : Float32 :=
  MIN (inv_sqrt_controller (1.0 / AC_PID.kP get_rate_yaw_pid) (AC_P.kP p._p_angle_yaw)
      (constrain_float (get_accel_yaw_max_radss p / 2.0) AC_ATTITUDE_ACCEL_Y_CONTROLLER_MIN_RADSS
        AC_ATTITUDE_ACCEL_Y_CONTROLLER_MAX_RADSS))
    AC_ATTITUDE_YAW_MAX_ERROR_ANGLE_RAD

/-- Comparisons with a zero do not see its sign. -/
theorem compare_zero_sign (a : UnpackedFloat) (s s' : Sign) :
    a.compare (.zero s) = a.compare (.zero s') := by
  cases a with
  | finite s1 _ _ _ => cases s1 <;> rfl
  | infinity s1 => cases s1 <;> rfl
  | _ => rfl

theorem lt_Z_iff {a z : Float32} (hz : Z z) : a < z ↔ a < 0 := by
  obtain ⟨s, hs⟩ := Z_unpack hz
  rw [Float32.lt_iff_unpack, Float32.lt_iff_unpack, hs, Float32.toModel_unpack_zero]
  unfold UnpackedFloat.lt
  rw [compare_zero_sign _ s .positive]

/-- **`thrust_heading_rotation_angles` of identity against identity** leaves the target, gives a
zero error and zero angles, provided the yaw-error cap is not negative (a property of the
parameters: it holds for positive `ATC_RAT_YAW_P`, `ATC_ANG_YAW_P` and acceleration limit, and it
is needed: with a negative cap `|0| > cap` holds and the zero error is clamped to `-cap ≠ 0`). -/
theorem thrust_heading_rotation_angles_Id (L : LibmZero32) (p : AC_AttitudeControl.Params)
    (get_rate_yaw_pid : AC_PID.Params) (hcap : ¬ (yaw_error_cap p get_rate_yaw_pid < 0))
    {target body : Quaternion} (ht : IdQ target) (hb : IdQ body) :
    (thrust_heading_rotation_angles p get_rate_yaw_pid target body).1 = target ∧
      ZV (thrust_heading_rotation_angles p get_rate_yaw_pid target body).2.1 ∧
      Z (thrust_heading_rotation_angles p get_rate_yaw_pid target body).2.2.1 ∧
      Z (thrust_heading_rotation_angles p get_rate_yaw_pid target body).2.2.2 := by
  obtain ⟨-, he, ha, hd⟩ := thrust_vector_rotation_angles_Id L ht hb
  unfold thrust_heading_rotation_angles
  generalize thrust_vector_rotation_angles target body = r at he ha hd
  obtain ⟨c, e, a, d⟩ := r
  simp only [] at he ha hd ⊢
  have hnot : ¬ (e.z.abs > yaw_error_cap p get_rate_yaw_pid) := by
    show ¬ (yaw_error_cap p get_rate_yaw_pid < e.z.abs)
    rw [lt_Z_iff (Z_abs he.2.2)]; exact hcap
  unfold yaw_error_cap at hnot
  simp only [hnot, decide_false, Bool.and_false, Bool.false_eq_true, if_false]
  split <;> exact ⟨rfl, he, ha, hd⟩

/-! ## Angle error to rate -/

/-- Bounded angle gains and P scales (`|·| ≤ 10⁹`) and a finite `_dt_s`. -/
structure AngOK (p : AC_AttitudeControl.Params) (s : AC_AttitudeControl.State) : Prop where
  kr : (AC_P.kP p._p_angle_roll).IsFinite
  kp : (AC_P.kP p._p_angle_pitch).IsFinite
  ky : (AC_P.kP p._p_angle_yaw).IsFinite
  krb : |(AC_P.kP p._p_angle_roll).toReal| ≤ 1e9
  kpb : |(AC_P.kP p._p_angle_pitch).toReal| ≤ 1e9
  kyb : |(AC_P.kP p._p_angle_yaw).toReal| ≤ 1e9
  sx : s._angle_P_scale.x.IsFinite
  sy : s._angle_P_scale.y.IsFinite
  sz : s._angle_P_scale.z.IsFinite
  sxb : |s._angle_P_scale.x.toReal| ≤ 1e9
  syb : |s._angle_P_scale.y.toReal| ≤ 1e9
  szb : |s._angle_P_scale.z.toReal| ≤ 1e9
  dt : s._dt_s.IsFinite

theorem gain_bound {k c : Float32} (hk : k.IsFinite) (hc : c.IsFinite) (hkb : |k.toReal| ≤ 1e9)
    (hcb : |c.toReal| ≤ 1e9) : (k * c).IsFinite ∧ |(k * c).toReal| ≤ 1e19 := by
  have hb : |k.toReal * c.toReal| ≤ 1e18 := by
    rw [abs_mul]; nlinarith [abs_nonneg k.toReal, abs_nonneg c.toReal]
  obtain ⟨h1, h2⟩ := mul_abs_le hk hc (hb.trans (by norm_num))
  exact ⟨h1, by linarith⟩

theorem rate_axis_Z {use : Bool} {acc k c err dt : Float32} {lo hi : Float32}
    (hlo : lo.IsFinite ∧ 0 < lo.toReal ∧ lo.toReal < 1) (hhi : hi.IsFinite ∧ 1 < hi.toReal ∧ hi.toReal < 13)
    (he : Z err) (hk : k.IsFinite) (hc : c.IsFinite) (hkb : |k.toReal| ≤ 1e9)
    (hcb : |c.toReal| ≤ 1e9) (hdt : dt.IsFinite) :
    Z (if (use && !is_zero acc) = true then
        sqrt_controller err (k * c) (constrain_float (acc / 2.0) lo hi) dt
      else k * c * err) := by
  obtain ⟨hgf, hgb⟩ := gain_bound hk hc hkb hcb
  split
  · obtain ⟨h1, h2⟩ := constrain_lits hlo hhi (acc / 2.0)
    exact sqrt_controller_Z he hgf h1 hdt hgb (h2.trans (by norm_num))
  · exact Z_mul_right hgf he

/-- **`update_ang_vel_target_from_att_error` at zero error** gives a zero rate demand. -/
theorem update_ang_vel_target_from_att_error_Z (p : AC_AttitudeControl.Params)
    (s : AC_AttitudeControl.State) (h : AngOK p s) {err : Vector3f} (he : ZV err) :
    ZV (update_ang_vel_target_from_att_error p s err) := by
  unfold update_ang_vel_target_from_att_error
  simp only []
  exact ⟨rate_axis_Z rp_min_spec rp_max_spec he.1 h.kr h.sx h.krb h.sxb h.dt,
    rate_axis_Z rp_min_spec rp_max_spec he.2.1 h.kp h.sy h.kpb h.syb h.dt,
    rate_axis_Z y_min_spec y_max_spec he.2.2 h.ky h.sz h.kyb h.szb h.dt⟩

/-- A symmetric clamp of a zero with a non-negative limit is a zero. -/
theorem constrain_sym_Z {x m : Float32} (hx : Z x) (hm : m.IsFinite) (h0 : 0 ≤ m.toReal) :
    Z (constrain_float x (-m) m) :=
  constrain_Z hx ((Float32.isFinite_neg m).2 hm) hm (by rw [Float32.toReal_neg]; linarith) h0

theorem len_not_gt {e : Vector3f} (ex : Z e.x) (ey : Z e.y) {r q : Float32} (hr : r.IsFinite)
    (hq : q.IsFinite) (hr' : is_zero r = false) (hq' : is_zero q = false) :
    ¬ ((⟨e.x / r, e.y / q⟩ : Vector2f).length > 1.0) := by
  have hr0 := abs_ge_of_not_zero hr hr'
  have hq0 := abs_ge_of_not_zero hq hq'
  have he := eps_pos
  have hl : Z (⟨e.x / r, e.y / q⟩ : Vector2f).length :=
    ZV2_length ⟨Z_div ex hr (fun h => by rw [h, abs_zero] at hr0; linarith),
      Z_div ey hq (fun h => by rw [h, abs_zero] at hq0; linarith)⟩
  show ¬ ((1.0 : Float32) < _)
  rw [lt_iff lit_one.1 hl.1, hl.2, lit_one.2]; norm_num

/-- **`ang_vel_limit` keeps a zero rate**, for finite non-negative limits. -/
theorem ang_vel_limit_Z {e : Vector3f} (he : ZV e) {r q y : Float32} (hr : r.IsFinite)
    (hq : q.IsFinite) (hy : y.IsFinite) (hr0 : 0 ≤ r.toReal) (hq0 : 0 ≤ q.toReal)
    (hy0 : 0 ≤ y.toReal) : ZV (ang_vel_limit e r q y) := by
  obtain ⟨ex, ey, ez⟩ := he
  unfold ang_vel_limit
  simp only []
  split_ifs
  all_goals first
    | (refine ⟨?_, ?_, ?_⟩ <;> first
        | with_reducible exact ex | with_reducible exact ey | with_reducible exact ez
        | with_reducible exact constrain_sym_Z ex hr hr0
        | with_reducible exact constrain_sym_Z ey hq hq0
        | with_reducible exact constrain_sym_Z ez hy hy0)
    | skip
  all_goals exfalso
  all_goals
    obtain ⟨hr', hq'⟩ := bool_or_false ‹¬(is_zero r || is_zero q) = true›
    exact len_not_gt ex ey hr hq hr' hq' ‹_›

/-! ## The attitude controller -/

theorem DEG_TO_RAD_spec : DEG_TO_RAD.IsFinite ∧ 0 < DEG_TO_RAD.toReal ∧ DEG_TO_RAD.toReal < 1 := by
  obtain ⟨h1, h2⟩ := litPos (x := DEG_TO_RAD) (m := 9370165) (e := -29) (hm := by decide) (by rfl)
  refine ⟨h1, ?_, ?_⟩ <;> rw [h2] <;> norm_num

/-- `radians(x)` of a finite `0 ≤ x ≤ 10³⁰` is finite and non-negative. -/
theorem radians_nonneg {x : Float32} (hx : x.IsFinite) (h0 : 0 ≤ x.toReal) (hb : x.toReal ≤ 1e30) :
    (radians x).IsFinite ∧ 0 ≤ (radians x).toReal := by
  obtain ⟨hd, hd0, hd1⟩ := DEG_TO_RAD_spec
  have hm : |x.toReal * DEG_TO_RAD.toReal| ≤ 1e38 := by
    rw [abs_of_nonneg (by positivity)]; nlinarith
  exact ⟨fin_mul hx hd hm, nonneg_mul hx hd hm (by positivity)⟩

/-- Finite non-negative rate limits `ATC_RATE_R_MAX`, `ATC_RATE_P_MAX`, `ATC_RATE_Y_MAX` (deg/s,
at most `10³⁰`). -/
structure RateMaxOK (prm : AC_AttitudeControl.Params) : Prop where
  roll : prm.ATC_RATE_R_MAX.IsFinite ∧ 0 ≤ prm.ATC_RATE_R_MAX.toReal ∧
    prm.ATC_RATE_R_MAX.toReal ≤ 1e30
  pitch : prm.ATC_RATE_P_MAX.IsFinite ∧ 0 ≤ prm.ATC_RATE_P_MAX.toReal ∧
    prm.ATC_RATE_P_MAX.toReal ≤ 1e30
  yaw : prm.ATC_RATE_Y_MAX.IsFinite ∧ 0 ≤ prm.ATC_RATE_Y_MAX.toReal ∧
    prm.ATC_RATE_Y_MAX.toReal ≤ 1e30

/-- **`attitude_controller_run_quat` at the hover fixed point.** With the body and the target at
the identity, a zero target angular velocity (the feed-forward), bounded angle gains and P scales,
finite non-negative rate limits and a non-negative yaw-error cap: the body-rate demand
`_ang_vel_body_rads` is a zero, the target stays, the thrust angles are zeros, the recorded error
`_attitude_ang_error` is the identity and the feed-forward scalar is `1.0`. -/
theorem attitude_controller_run_quat_Z (L : LibmZero32) (p : AC_AttitudeControl.Params)
    (get_rate_yaw_pid : AC_PID.Params) (hcap : ¬ (yaw_error_cap p get_rate_yaw_pid < 0))
    (hrm : RateMaxOK p) (s : AC_AttitudeControl.State) (hang : AngOK p s)
    (ht : IdQ s._attitude_target) (hff : ZV s._ang_vel_target_rads) {body : Quaternion}
    (hb : IdQ body) :
    ZV (attitude_controller_run_quat p get_rate_yaw_pid s body)._ang_vel_body_rads ∧
      (attitude_controller_run_quat p get_rate_yaw_pid s body)._attitude_target =
        s._attitude_target ∧
      Z (attitude_controller_run_quat p get_rate_yaw_pid s body)._thrust_angle_rad ∧
      Z (attitude_controller_run_quat p get_rate_yaw_pid s body)._thrust_error_angle_rad ∧
      IdQ (attitude_controller_run_quat p get_rate_yaw_pid s body)._attitude_ang_error ∧
      (attitude_controller_run_quat p get_rate_yaw_pid s body)._feedforward_scalar = 1.0 ∧
      (attitude_controller_run_quat p get_rate_yaw_pid s body)._ang_vel_target_rads =
        s._ang_vel_target_rads ∧
      (attitude_controller_run_quat p get_rate_yaw_pid s body)._ang_accel_target_rads =
        s._ang_accel_target_rads ∧
      (attitude_controller_run_quat p get_rate_yaw_pid s body)._euler_rate_target_rads =
        s._euler_rate_target_rads ∧
      (attitude_controller_run_quat p get_rate_yaw_pid s body)._euler_angle_target_rad =
        s._euler_angle_target_rad := by
  obtain ⟨h1, he, ha, hd⟩ := thrust_heading_rotation_angles_Id L p get_rate_yaw_pid hcap ht hb
  unfold attitude_controller_run_quat
  generalize thrust_heading_rotation_angles p get_rate_yaw_pid s._attitude_target body = r
    at h1 he ha hd
  obtain ⟨c, e, a, d⟩ := r
  simp only [] at h1 he ha hd ⊢
  subst h1
  have n1 : ¬ (d > AC_ATTITUDE_THRUST_ERROR_ANGLE_RAD * 2.0) := by
    show ¬ (_ < d); rw [lt_iff thrust_err2_spec.1 hd.1, hd.2]; linarith [thrust_err2_spec.2]
  have n2 : ¬ (d > AC_ATTITUDE_THRUST_ERROR_ANGLE_RAD) := by
    show ¬ (_ < d); rw [lt_iff thrust_err_spec.1 hd.1, hd.2]; linarith [thrust_err_spec.2]
  simp only [n1, n2, if_false]
  obtain ⟨rf, r0⟩ := radians_nonneg hrm.roll.1 hrm.roll.2.1 hrm.roll.2.2
  obtain ⟨qf, q0⟩ := radians_nonneg hrm.pitch.1 hrm.pitch.2.1 hrm.pitch.2.2
  obtain ⟨yf, y0⟩ := radians_nonneg hrm.yaw.1 hrm.yaw.2.1 hrm.yaw.2.2
  have hw : ZV (ang_vel_limit (update_ang_vel_target_from_att_error p
      { s with _thrust_angle_rad := a, _thrust_error_angle_rad := d } e)
      (radians p._ang_vel_roll_max_degs) (radians p._ang_vel_pitch_max_degs)
      (radians p._ang_vel_yaw_max_degs)) :=
    ang_vel_limit_Z (update_ang_vel_target_from_att_error_Z p _
      ⟨hang.kr, hang.kp, hang.ky, hang.krb, hang.kpb, hang.kyb, hang.sx, hang.sy, hang.sz,
        hang.sxb, hang.syb, hang.szb, hang.dt⟩ he) rf qf yf r0 q0 y0
  have hf : ZV (body.inverse * s._attitude_target * s._ang_vel_target_rads) :=
    ZV_of_SameV (mul_vec_Id (mul_Id (inverse_Id hb) ht) hff.fin) hff
  exact ⟨ZV_add hw hf, trivial, ha, hd, mul_Id (inverse_Id hb) ht, trivial, trivial, trivial,
    trivial, trivial⟩

end Contracts.CopterZero
