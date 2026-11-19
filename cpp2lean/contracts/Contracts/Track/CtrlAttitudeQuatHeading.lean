import Contracts.Track.CtrlAttitudeBase

/-!
# `thrust_heading_rotation_angles` with the heading clip inactive (milestone M4, lemma C8)

`AC_AttitudeControl::thrust_heading_rotation_angles` splits the attitude error into a thrust-vector
part and a heading part (`thrust_vector_rotation_angles`) and then, when the heading error exceeds
`heading_error_max`, clips it and moves the attitude target towards the body attitude. This file
evaluates the clip threshold for the mission's yaw tuning and shows that below it the function
returns the attitude target unchanged together with the outputs of
`thrust_vector_rotation_angles`.

With `_pid_rate_yaw._kp = 0.3`, `_p_angle_yaw._kp = 4.5` and `_accel_yaw_max_degss = 270`:

* `heading_accel_max = constrain_value(radians(270)/2, radians(10), radians(120))` is the upper
  bound `radians(120)`, since `radians(270)/2 ≈ 2.356 > radians(120) ≈ 2.094`;
* `inv_sqrt_controller(1/0.3, 4.5, radians(120))` takes its last branch and is `≈ 2.704`, above
  `radians(45) ≈ 0.785`, so `heading_error_max = MIN(…, radians(45)) = radians(45)`;
* `radians(45)` is within `4·10⁻⁷` of `π/4` (the `float` value of `π` is only known up to the
  rounding of `LibmSpec.f64ToF32`, `pi32`).

The result of `thrust_vector_rotation_angles` is left opaque: the main theorem assumes its heading
error is finite and at most `radians(45)` in magnitude.
-/

namespace Contracts.Track.AttHeading

open Contracts.Mission AC_Attitude_lib Float.Model UnpackedFloat Contracts.Track.Att

noncomputable section

/-! ## Literals -/

theorem lit_unpack_0p3 : (0.300000012 : Float32).toModel.unpack = .finite .positive 10066330 (-25) (by decide) := by rfl
theorem lit_toReal_0p3 : (0.300000012 : Float32).toReal = (10066330 / 33554432 : ℝ) := by
  rw [Float32.toReal, lit_unpack_0p3]; simp [UnpackedFloat.toReal, Sign.apply]; norm_num
theorem lit_isFinite_0p3 : (0.300000012 : Float32).IsFinite := by
  rw [Float32.isFinite_iff, lit_unpack_0p3]; rfl

theorem lit_unpack_270 : (270.0 : Float32).toModel.unpack = .finite .positive 8847360 (-15) (by decide) := by rfl
theorem lit_toReal_270 : (270.0 : Float32).toReal = (270 : ℝ) := by
  rw [Float32.toReal, lit_unpack_270]; simp [UnpackedFloat.toReal, Sign.apply]; norm_num
theorem lit_isFinite_270 : (270.0 : Float32).IsFinite := by
  rw [Float32.isFinite_iff, lit_unpack_270]; rfl

theorem lit_unpack_120 : (120.0 : Float32).toModel.unpack = .finite .positive 15728640 (-17) (by decide) := by rfl
theorem lit_toReal_120 : (120.0 : Float32).toReal = (120 : ℝ) := by
  rw [Float32.toReal, lit_unpack_120]; simp [UnpackedFloat.toReal, Sign.apply]; norm_num
theorem lit_isFinite_120 : (120.0 : Float32).IsFinite := by
  rw [Float32.isFinite_iff, lit_unpack_120]; rfl

theorem lit_unpack_45 : (45.0 : Float32).toModel.unpack = .finite .positive 11796480 (-18) (by decide) := by rfl
theorem lit_toReal_45 : (45.0 : Float32).toReal = (45 : ℝ) := by
  rw [Float32.toReal, lit_unpack_45]; simp [UnpackedFloat.toReal, Sign.apply]; norm_num
theorem lit_isFinite_45 : (45.0 : Float32).IsFinite := by
  rw [Float32.isFinite_iff, lit_unpack_45]; rfl

theorem lit_unpack_4p5 : (4.5 : Float32).toModel.unpack = .finite .positive 9437184 (-21) (by decide) := by rfl
theorem lit_toReal_4p5 : (4.5 : Float32).toReal = (9 / 2 : ℝ) := by
  rw [Float32.toReal, lit_unpack_4p5]; simp [UnpackedFloat.toReal, Sign.apply]; norm_num
theorem lit_isFinite_4p5 : (4.5 : Float32).IsFinite := by
  rw [Float32.isFinite_iff, lit_unpack_4p5]; rfl

/-- `(float) 1.0` is `1` (`LibmSpec.f64ToF32_exact`). -/
theorem one32 (hL : LibmSpec) : A32 (Float.toFloat32 (1.0 : Float)) 1 0 := by
  obtain ⟨f, e⟩ := hL.f64ToF32_exact (1.0 : Float) (1.0 : Float32) f64_isFinite_1p0 f32_isFinite_1p0
    (by rw [f32_toReal_1p0, f64_toReal_1p0])
  exact ⟨f, by rw [e, f64_toReal_1p0]; simp⟩

/-- `(float) 2.0` is `2` (`LibmSpec.f64ToF32_exact`). -/
theorem two32 (hL : LibmSpec) : A32 (Float.toFloat32 (2.0 : Float)) 2 0 := by
  obtain ⟨f, e⟩ := hL.f64ToF32_exact (2.0 : Float) (2.0 : Float32) f64_isFinite_2p0 f32_isFinite_2p0
    (by rw [f32_toReal_2p0, f64_toReal_2p0])
  exact ⟨f, by rw [e, f64_toReal_2p0]; simp⟩

theorem lit (x : Float32) (r : ℝ) (hf : x.IsFinite) (hr : x.toReal = r) : A32 x r 0 :=
  (A32.of_exact hf).congr hr

/-! ## `radians` -/

/-- The factor `(float) M_PI / 180.0f` of `radians`. -/
theorem deg32 (hL : LibmSpec) :
    A32 (Float.toFloat32 (3.1415926535897931 : Float) / (180.0 : Float32)) (piD / 180) (3 / 10 ^ 9) := by
  have hp : A32 (Float.toFloat32 (3.1415926535897931 : Float)) piD (2 / 10 ^ 7) := by
    refine (pi32 hL).mono ?_
    have := η32_small
    have h1 : (1 / 16777216 : ℝ) * piD ≤ 19 / 10 ^ 8 := by norm_num [piD]
    rw [u32_eq]; linarith
  exact A32.div_c (Ra := 4) (m := 180) (Q := 1 / 50) hp (lit _ 180 f32_isFinite_180p0 f32_toReal_180p0)
    (abs_le.2 ⟨by norm_num [piD], by norm_num [piD]⟩) (by norm_num) (by norm_num) le_rfl
    (abs_le.2 ⟨by norm_num [piD], by norm_num [piD]⟩) (by norm_num [capF]) (by norm_num)

/-- `radians` of a `float` in `[0, 360]`. -/
theorem radians_approx (hL : LibmSpec) {x : Float32} {X e : ℝ} (hx : x.IsFinite)
    (hX : x.toReal = X) (h0 : 0 ≤ X) (h1 : X ≤ 360)
    (he : X * (3 / 10 ^ 9) + 1 / 50 * 0 + 0 * (3 / 10 ^ 9) +
      1 / 16777216 * (X * (1 / 50) + (X * (3 / 10 ^ 9) + 1 / 50 * 0 + 0 * (3 / 10 ^ 9))) +
      1 / 10 ^ 40 ≤ e) :
    A32 (radians_float x) (X * (piD / 180)) e := by
  have hc : (1000 : ℝ) ≤ capF := by norm_num [capF]
  exact A32.mul_c (Ra := X) (Rb := 1 / 50) (lit x X hx hX) (deg32 hL) (by rw [abs_of_nonneg h0])
    (abs_le.2 ⟨by norm_num [piD], by norm_num [piD]⟩) le_rfl (by norm_num) (by nlinarith) he

theorem rad270 (hL : LibmSpec) : A32 (radians_float 270.0) (270 * (piD / 180)) (2 / 10 ^ 6) :=
  radians_approx hL lit_isFinite_270 lit_toReal_270 (by norm_num) (by norm_num) (by norm_num)

theorem rad120 (hL : LibmSpec) : A32 (radians_float 120.0) (120 * (piD / 180)) (1 / 10 ^ 6) :=
  radians_approx hL lit_isFinite_120 lit_toReal_120 (by norm_num) (by norm_num) (by norm_num)

theorem rad10 (hL : LibmSpec) : A32 (radians_float 10.0) (10 * (piD / 180)) (1 / 10 ^ 6) :=
  radians_approx hL f32_isFinite_10p0 f32_toReal_10p0 (by norm_num) (by norm_num) (by norm_num)

theorem rad45 (hL : LibmSpec) : A32 (radians_float 45.0) (45 * (piD / 180)) (3 / 10 ^ 7) :=
  radians_approx hL lit_isFinite_45 lit_toReal_45 (by norm_num) (by norm_num) (by norm_num)

/-- **Value lemma.** `radians(45.0f)` is finite and within `4·10⁻⁷` of `π/4`. -/
theorem radians45_pi4 (hL : LibmSpec) : A32 (radians_float 45.0) (Real.pi / 4) (4 / 10 ^ 7) := by
  have h := rad45 hL
  refine ⟨h.1, ?_⟩
  have h1 := h.2
  have h2 := piD_close
  have : |(radians_float 45.0).toReal - Real.pi / 4| ≤
      |(radians_float 45.0).toReal - 45 * (piD / 180)| + |piD - Real.pi| / 4 := by
    have := abs_sub_le (radians_float 45.0).toReal (45 * (piD / 180)) (Real.pi / 4)
    have e : |45 * (piD / 180) - Real.pi / 4| = |piD - Real.pi| / 4 := by
      rw [show 45 * (piD / 180) - Real.pi / 4 = (piD - Real.pi) / 4 by ring, abs_div,
        abs_of_pos (by norm_num : (0 : ℝ) < 4)]
    linarith
  linarith

/-- The same, with the error bound `10⁻⁶` and as two-sided bounds. -/
theorem radians45_bounds (hL : LibmSpec) :
    (radians_float 45.0).IsFinite ∧ Real.pi / 4 - 1 / 10 ^ 6 ≤ (radians_float 45.0).toReal ∧
      (radians_float 45.0).toReal ≤ Real.pi / 4 + 1 / 10 ^ 6 := by
  have h := radians45_pi4 hL
  have := abs_le.1 h.2
  exact ⟨h.1, by linarith, by linarith⟩

/-! ## `constrain_value`, `MIN`, `inv_sqrt_controller` -/

/-- Above the upper bound, `constrain_value` returns the upper bound. -/
theorem constrain_above {amt low high : Float32} (line : UInt32) (ha : amt.IsFinite)
    (hl : low.IsFinite) (hh : high.IsFinite) (h1 : low.toReal ≤ amt.toReal)
    (h2 : high.toReal < amt.toReal) :
    constrain_value_line_float amt low high line = high := by
  simp only [constrain_value_line_float, Id.run, Contracts.Mission.Float32.isNaN_of_isFinite ha,
    Bool.false_eq_true, ite_false, id_pure_eq]
  rw [ite_eq_right (fun h => absurd ((Float32.lt_iff_toReal_lt ha hl).1 h) (not_lt.2 h1)),
    ite_eq_left ((Float32.lt_iff_toReal_lt hh ha).2 h2)]

/-- `MIN(a, b) = b` when `b ≤ a`. -/
theorem min_right {a b : Float32} (ha : a.IsFinite) (hb : b.IsFinite) (h : b.toReal ≤ a.toReal) :
    MIN_float2 a b = b := by
  show (if a < b then a else b) = b
  rw [ite_eq_right (fun h' => absurd ((Float32.lt_iff_toReal_lt ha hb).1 h') (not_lt.2 h))]

/-- The last branch of `inv_sqrt_controller`, for a positive `output` beyond the linear region. -/
theorem inv_sqrt_last {o p D : Float32} (hzp : is_zero_float p = false)
    (hnD : is_negative_float D = false) (hzD : is_zero_float D = false)
    (hab : ¬ Float32.abs o < D / p) (hpo : is_positive_float o = true) :
    inv_sqrt_controller o p D =
      D / sq_float p * (0.5 : Float32) + sq_float o / (Float.toFloat32 (2.0 : Float) * D) := by
  simp only [inv_sqrt_controller, Id.run, hzp, hnD, hzD, hpo, Bool.and_false, Bool.or_false,
    Bool.not_false, Bool.and_true, Bool.false_eq_true, ite_false, ite_true, ite_eq_right hab]
  rfl

/-! ## The two thresholds -/

section
variable (p : AC_AttitudeControl_Multi.Params)

/-- `radians(270)/2` with `(float) π`. -/
theorem half270 (hL : LibmSpec) :
    A32 (radians_float 270.0 / (2.0 : Float32)) (270 * (piD / 180) / 2) (2 / 10 ^ 6) :=
  A32.div_c (Ra := 5) (m := 2) (Q := 3) (rad270 hL) (lit _ 2 f32_isFinite_2p0 f32_toReal_2p0)
    (abs_le.2 ⟨by norm_num [piD], by norm_num [piD]⟩) (by norm_num) (by norm_num) le_rfl
    (abs_le.2 ⟨by norm_num [piD], by norm_num [piD]⟩) (by norm_num [capF]) (by norm_num)

/-- **C8, `heading_accel_max`.** With `_accel_yaw_max_degss = 270`, the yaw acceleration bound
`constrain_value(get_accel_yaw_max_radss() / 2, radians(10), radians(120))` is `radians(120)`. -/
theorem heading_accel_max (hL : LibmSpec) (h3 : p._accel_yaw_max_degss = (270.0 : Float32))
    (line : UInt32) :
    constrain_value_line_float (AC_AttitudeControl_Multi.get_accel_yaw_max_radss p / (2.0 : Float32))
      (radians_float 10.0) (radians_float 120.0) line = radians_float 120.0 := by
  rw [show AC_AttitudeControl_Multi.get_accel_yaw_max_radss p = radians_float 270.0 by
    rw [← h3]; rfl]
  have ha := half270 hL
  have hl := rad10 hL
  have hh := rad120 hL
  have a1 := abs_le.1 ha.2
  have a2 := abs_le.1 hl.2
  have a3 := abs_le.1 hh.2
  unfold piD at a1 a2 a3
  exact constrain_above line ha.1 hl.1 hh.1 (by linarith) (by linarith)

/-- `1.0f / 0.3f`. -/
theorem out_approx (hL : LibmSpec) :
    A32 (Float.toFloat32 (1.0 : Float) / (0.300000012 : Float32)) (1 / (10066330 / 33554432))
      (1 / 10 ^ 6) :=
  A32.div_c (Ra := 1) (m := 3 / 10) (Q := 4) (one32 hL) (lit _ _ lit_isFinite_0p3 lit_toReal_0p3)
    (by norm_num) (by norm_num) (le_abs.2 (Or.inl (by norm_num))) le_rfl
    (abs_le.2 ⟨by norm_num, by norm_num⟩) (by norm_num [capF]) (by norm_num)

/-- `inv_sqrt_controller(1/0.3, 4.5, radians(120))` is above `2.7`. -/
theorem inv_sqrt_val (hL : LibmSpec) :
    (inv_sqrt_controller (Float.toFloat32 (1.0 : Float) / (0.300000012 : Float32)) (4.5 : Float32)
      (radians_float 120.0)).IsFinite ∧
    27 / 10 ≤ (inv_sqrt_controller (Float.toFloat32 (1.0 : Float) / (0.300000012 : Float32))
      (4.5 : Float32) (radians_float 120.0)).toReal := by
  have ho := out_approx hL
  have hD := rad120 hL
  have hp := lit _ _ lit_isFinite_4p5 lit_toReal_4p5
  have aD := abs_le.1 hD.2
  have ao := abs_le.1 ho.2
  unfold piD at aD
  -- the branch conditions
  have hzp : is_zero_float (4.5 : Float32) = false :=
    isZero_false lit_isFinite_4p5 (by rw [lit_toReal_4p5, abs_of_pos (by norm_num)]; norm_num)
  have hnD : is_negative_float (radians_float 120.0) = false :=
    Att.isNeg_false hL hD.1 (by have : (0 : ℝ) ≤ 2 ^ (-24 : ℤ) := by positivity
                                linarith)
  have hzD : is_zero_float (radians_float 120.0) = false :=
    isZero_false hD.1 (by rw [abs_of_pos (by linarith)]; norm_num; linarith)
  have hpo : is_positive_float (Float.toFloat32 (1.0 : Float) / (0.300000012 : Float32)) = true :=
    isPos_true ho.1 (by norm_num at ao ⊢; linarith)
  have hlv : A32 (radians_float 120.0 / (4.5 : Float32)) (120 * (piD / 180) / (9 / 2)) (1 / 10 ^ 5) :=
    A32.div_c (Ra := 3) (m := 4) (Q := 1) hD hp
      (abs_le.2 ⟨by norm_num [piD], by norm_num [piD]⟩) (by norm_num) (le_abs.2 (Or.inl (by norm_num)))
      le_rfl (abs_le.2 ⟨by norm_num [piD], by norm_num [piD]⟩) (by norm_num [capF]) (by norm_num)
  have alv := abs_le.1 hlv.2
  unfold piD at alv
  have hab : ¬ Float32.abs (Float.toFloat32 (1.0 : Float) / (0.300000012 : Float32)) <
      radians_float 120.0 / (4.5 : Float32) := by
    rw [Float32.lt_iff_toReal_lt ((Float32.isFinite_abs _).2 ho.1) hlv.1, Float32.toReal_abs,
      abs_of_pos (by norm_num at ao; linarith)]
    norm_num at ao alv ⊢; linarith
  rw [inv_sqrt_last hzp hnD hzD hab hpo]
  -- the stopping distance
  have hsq : A32 (sq_float (4.5 : Float32)) (9 / 2 * (9 / 2)) (1 / 10 ^ 5) :=
    A32.mul_c (Ra := 5) (Rb := 5) hp hp (abs_le.2 ⟨by norm_num, by norm_num⟩)
      (abs_le.2 ⟨by norm_num, by norm_num⟩) le_rfl le_rfl (by norm_num [capF]) (by norm_num)
  have hld : A32 (radians_float 120.0 / sq_float (4.5 : Float32))
      (120 * (piD / 180) / (9 / 2 * (9 / 2))) (1 / 10 ^ 5) :=
    A32.div_c (Ra := 3) (m := 20) (Q := 1 / 5) hD hsq
      (abs_le.2 ⟨by norm_num [piD], by norm_num [piD]⟩) (by norm_num) (le_abs.2 (Or.inl (by norm_num)))
      (by norm_num) (abs_le.2 ⟨by norm_num [piD], by norm_num [piD]⟩) (by norm_num [capF]) (by norm_num)
  have hld2 : A32 (radians_float 120.0 / sq_float (4.5 : Float32) * (0.5 : Float32))
      (120 * (piD / 180) / (9 / 2 * (9 / 2)) * (1 / 2)) (1 / 10 ^ 4) :=
    A32.mul_c (Ra := 1 / 5) (Rb := 1) hld (lit _ _ f32_isFinite_0p5 f32_toReal_0p5)
      (abs_le.2 ⟨by norm_num [piD], by norm_num [piD]⟩) (abs_le.2 ⟨by norm_num, by norm_num⟩)
      (by norm_num) le_rfl (by norm_num [capF]) (by norm_num)
  have hso : A32 (sq_float (Float.toFloat32 (1.0 : Float) / (0.300000012 : Float32)))
      (1 / (10066330 / 33554432) * (1 / (10066330 / 33554432))) (1 / 10 ^ 4) :=
    A32.mul_c (Ra := 4) (Rb := 4) ho ho (abs_le.2 ⟨by norm_num, by norm_num⟩)
      (abs_le.2 ⟨by norm_num, by norm_num⟩) (by norm_num) (by norm_num) (by norm_num [capF])
      (by norm_num)
  have h2D : A32 (Float.toFloat32 (2.0 : Float) * radians_float 120.0) (2 * (120 * (piD / 180)))
      (1 / 10 ^ 5) :=
    A32.mul_c (Ra := 2) (Rb := 3) (two32 hL) hD (abs_le.2 ⟨by norm_num, by norm_num⟩)
      (abs_le.2 ⟨by norm_num [piD], by norm_num [piD]⟩) le_rfl (by norm_num) (by norm_num [capF])
      (by norm_num)
  have hq : A32 (sq_float (Float.toFloat32 (1.0 : Float) / (0.300000012 : Float32)) /
      (Float.toFloat32 (2.0 : Float) * radians_float 120.0))
      (1 / (10066330 / 33554432) * (1 / (10066330 / 33554432)) / (2 * (120 * (piD / 180))))
      (1 / 10 ^ 4) :=
    A32.div_c (Ra := 12) (m := 4) (Q := 3) hso h2D (abs_le.2 ⟨by norm_num, by norm_num⟩)
      (by norm_num) (le_abs.2 (Or.inl (by norm_num [piD]))) (by norm_num)
      (abs_le.2 ⟨by norm_num [piD], by norm_num [piD]⟩) (by norm_num [capF]) (by norm_num)
  have hsd := A32.add_c (R := 3) hld2 hq (abs_le.2 ⟨by norm_num [piD], by norm_num [piD]⟩)
    (by norm_num [capF]) (le_refl _)
  have asd := abs_le.1 hsd.2
  unfold piD at asd
  refine ⟨hsd.1, ?_⟩
  norm_num at asd ⊢
  linarith

/-- **C8, `heading_error_max`.** With the yaw tuning `0.3`, `4.5`, `270`, the heading error bound
`MIN(inv_sqrt_controller(1/kP_rate_yaw, kP_angle_yaw, heading_accel_max), radians(45))` is
`radians(45)`. -/
theorem heading_error_max (hL : LibmSpec)
    (h1 : p._pid_rate_yaw._kp = (0.300000012 : Float32))
    (h2 : p._p_angle_yaw._kp = (4.5 : Float32))
    (h3 : p._accel_yaw_max_degss = (270.0 : Float32)) (line : UInt32) :
    MIN_float2
      (inv_sqrt_controller (Float.toFloat32 (1.0 : Float) / p._pid_rate_yaw._kp) p._p_angle_yaw._kp
        (constrain_value_line_float
          (AC_AttitudeControl_Multi.get_accel_yaw_max_radss p / (2.0 : Float32))
          (radians_float 10.0) (radians_float 120.0) line))
      (radians_float 45.0) = radians_float 45.0 := by
  rw [heading_accel_max p hL h3, h1, h2]
  have hv := inv_sqrt_val hL
  have h45 := radians45_bounds hL
  have := Real.pi_lt_d2
  exact min_right hv.1 h45.1 (by linarith)

end

/-! ## The main theorem -/

/-- **C8, clip inactive.** With the yaw tuning `_pid_rate_yaw._kp = 0.3`,
`_p_angle_yaw._kp = 4.5`, `_accel_yaw_max_degss = 270`: when the heading error computed by
`thrust_vector_rotation_angles` (from the zero correction quaternion `Quaternion.init_void`) is
finite and at most `radians(45)` in magnitude, `thrust_heading_rotation_angles` returns the attitude
target unchanged and the attitude error, thrust angle and thrust error angle of
`thrust_vector_rotation_angles`. -/
theorem thrust_heading_clip_inactive (hL : LibmSpec) (p : AC_AttitudeControl_Multi.Params)
    (h1 : p._pid_rate_yaw._kp = (0.300000012 : Float32))
    (h2 : p._p_angle_yaw._kp = (4.5 : Float32))
    (h3 : p._accel_yaw_max_degss = (270.0 : Float32))
    (target body : Quaternion.State) (err : Vector3f.State) (ta tea : Float32)
    (hz : (AC_AttitudeControl_Multi.thrust_vector_rotation_angles target body Quaternion.init_void
      err ta tea).2.1.z.IsFinite)
    (hle : |(AC_AttitudeControl_Multi.thrust_vector_rotation_angles target body Quaternion.init_void
      err ta tea).2.1.z.toReal| ≤ (radians_float 45.0).toReal) :
    AC_AttitudeControl_Multi.thrust_heading_rotation_angles p target body err ta tea =
      (target,
        (AC_AttitudeControl_Multi.thrust_vector_rotation_angles target body Quaternion.init_void
          err ta tea).2.1,
        (AC_AttitudeControl_Multi.thrust_vector_rotation_angles target body Quaternion.init_void
          err ta tea).2.2.1,
        (AC_AttitudeControl_Multi.thrust_vector_rotation_angles target body Quaternion.init_void
          err ta tea).2.2.2) := by
  simp only [AC_AttitudeControl_Multi.thrust_heading_rotation_angles, Id.run]
  rw [heading_error_max p hL h1 h2 h3]
  have hd : decide (Float32.abs (AC_AttitudeControl_Multi.thrust_vector_rotation_angles target body
      Quaternion.init_void err ta tea).2.1.z > radians_float 45.0) = false := by
    rw [decide_eq_false_iff_not]
    intro h
    have := (Float32.lt_iff_toReal_lt (radians45_bounds hL).1 ((Float32.isFinite_abs _).2 hz)).1 h
    rw [Float32.toReal_abs] at this
    linarith
  rw [hd, Bool.and_false]
  simp

/-- The same with the hypothesis `|heading error| ≤ π/4 - 10⁻⁶`, free of the `float` value of
`radians(45)`. -/
theorem thrust_heading_clip_inactive_pi (hL : LibmSpec) (p : AC_AttitudeControl_Multi.Params)
    (h1 : p._pid_rate_yaw._kp = (0.300000012 : Float32))
    (h2 : p._p_angle_yaw._kp = (4.5 : Float32))
    (h3 : p._accel_yaw_max_degss = (270.0 : Float32))
    (target body : Quaternion.State) (err : Vector3f.State) (ta tea : Float32)
    (hz : (AC_AttitudeControl_Multi.thrust_vector_rotation_angles target body Quaternion.init_void
      err ta tea).2.1.z.IsFinite)
    (hle : |(AC_AttitudeControl_Multi.thrust_vector_rotation_angles target body Quaternion.init_void
      err ta tea).2.1.z.toReal| ≤ Real.pi / 4 - 1 / 10 ^ 6) :
    AC_AttitudeControl_Multi.thrust_heading_rotation_angles p target body err ta tea =
      (target,
        (AC_AttitudeControl_Multi.thrust_vector_rotation_angles target body Quaternion.init_void
          err ta tea).2.1,
        (AC_AttitudeControl_Multi.thrust_vector_rotation_angles target body Quaternion.init_void
          err ta tea).2.2.1,
        (AC_AttitudeControl_Multi.thrust_vector_rotation_angles target body Quaternion.init_void
          err ta tea).2.2.2) :=
  thrust_heading_clip_inactive hL p h1 h2 h3 target body err ta tea hz
    (hle.trans (radians45_bounds hL).2.1)

end

end Contracts.Track.AttHeading
