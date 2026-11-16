import Contracts.Track.CtrlAttitudeRate

/-!
# C10: the angle loop of the attitude controller in `float` (milestone M4)

With the mission's parameters (`ATC_ANG_RLL_P = ATC_ANG_PIT_P = 9`, `ATC_ANG_YAW_P = 4.5`,
`ATC_ACCEL_R_MAX = ATC_ACCEL_P_MAX = 1800 deg/s²`, `ATC_ACCEL_Y_MAX = 270 deg/s²`,
`ATC_RATE_*_MAX = 0`, square-root controller on, angle-P scale `1`, `dt = 1/400`):

* `radians_zero`, `ang_vel_limit_zero`, `ang_vel_limit_mission`: `ang_vel_limit` with the three
  limits `radians(0)` returns its argument unchanged;
* `sqrt_ctrl_linear`: `sqrt_controller(e, p, lim, dt)` in its linear zone
  `|e| ≤ (lim / p²)(1 - 2⁻²⁰)` with `1 ≤ p ≤ 16` and `p dt ≤ 1` (the rate clamp `|e| / dt` is
  inactive) returns the `float` product `e * p`, within `2⁻²⁴ |p e| + 2⁻¹⁵⁰` of `p e`;
* `accel_lim_rp`, `accel_lim_y`: the second-order limits the code passes: roll and pitch
  `constrain(radians(1800) / 2, radians(40), radians(720)) = radians(720) ≈ 12.566` (the upper
  bound is active), yaw `constrain(radians(270) / 2, radians(10), radians(120)) = radians(120) ≈
  2.094` (the upper bound is active: `radians(270) / 2 ≈ 2.356 > 2.094`). The linear zones are
  `|e| ≤ 0.155 rad` (roll, pitch: `12.566 / 81 ≈ 0.1551`) and `|e| ≤ 0.1034 rad` (yaw:
  `2.0944 / 20.25 ≈ 0.10343`);
* `ang_vel_target_spec`: `update_ang_vel_target_from_att_error` is `(9 e.x, 9 e.y, 4.5 e.z)` up to
  `10⁻⁷` per component in those zones;
* `attitude_run_quat_eq`: in `attitude_controller_run_quat`, when the thrust error angle is at most
  `radians(30)`, the body-rate target is the `float` sum of the limited angle-P output and the
  feed-forward rotation, and `_feedforward_scalar = 1`.
-/

namespace Contracts.Track.Att

open Float.Model UnpackedFloat Contracts.Mission AC_Attitude_lib

noncomputable section

/-! ## Literals -/

theorem f32_unpack_30p0 : (30.0 : Float32).toModel.unpack = .finite .positive 15728640 (-19) (by decide) := by rfl
theorem f32_toReal_30p0 : (30.0 : Float32).toReal = (30 : ℝ) := by
  rw [Float32.toReal, f32_unpack_30p0]; simp [UnpackedFloat.toReal, Sign.apply]; norm_num
theorem f32_isFinite_30p0 : (30.0 : Float32).IsFinite := by
  rw [Float32.isFinite_iff, f32_unpack_30p0]; rfl

theorem f32_unpack_40p0 : (40.0 : Float32).toModel.unpack = .finite .positive 10485760 (-18) (by decide) := by rfl
theorem f32_toReal_40p0 : (40.0 : Float32).toReal = (40 : ℝ) := by
  rw [Float32.toReal, f32_unpack_40p0]; simp [UnpackedFloat.toReal, Sign.apply]; norm_num
theorem f32_isFinite_40p0 : (40.0 : Float32).IsFinite := by
  rw [Float32.isFinite_iff, f32_unpack_40p0]; rfl

theorem f32_unpack_720p0 : (720.0 : Float32).toModel.unpack = .finite .positive 11796480 (-14) (by decide) := by rfl
theorem f32_toReal_720p0 : (720.0 : Float32).toReal = (720 : ℝ) := by
  rw [Float32.toReal, f32_unpack_720p0]; simp [UnpackedFloat.toReal, Sign.apply]; norm_num
theorem f32_isFinite_720p0 : (720.0 : Float32).IsFinite := by
  rw [Float32.isFinite_iff, f32_unpack_720p0]; rfl

theorem f32_unpack_120p0 : (120.0 : Float32).toModel.unpack = .finite .positive 15728640 (-17) (by decide) := by rfl
theorem f32_toReal_120p0 : (120.0 : Float32).toReal = (120 : ℝ) := by
  rw [Float32.toReal, f32_unpack_120p0]; simp [UnpackedFloat.toReal, Sign.apply]; norm_num
theorem f32_isFinite_120p0 : (120.0 : Float32).IsFinite := by
  rw [Float32.isFinite_iff, f32_unpack_120p0]; rfl

/-! ## `radians` -/

/-- `(float) M_PI / 180`, the factor of `radians`: within `2.2·10⁻⁹` of `piD / 180`. -/
theorem deg32 (hL : LibmSpec) :
    B32 (Float.toFloat32 (3.1415926535897931 : Float) / (180.0 : Float32)) (piD / 180)
      (22 / 10000000000) (7 / 400) := by
  have hpi := pi32 hL
  have bpi : B32 (Float.toFloat32 (3.1415926535897931 : Float)) piD (19 / 100000000) (315 / 100) :=
    ⟨hpi.mono (by rw [u32_eq, η32_eq]; norm_num [piD]),
      by rw [abs_of_pos (by norm_num [piD])]; norm_num [piD]⟩
  have b180 : B32 (180.0 : Float32) 180 0 180 :=
    B32.lit f32_isFinite_180p0 f32_toReal_180p0 (by norm_num)
  exact B32.div (mlo := 180) bpi b180 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [capF]) (by norm_num)

/-- `radians(x)` of a literal `x = v` with `|v| ≤ V`. -/
theorem radians_b32 (hL : LibmSpec) {x : Float32} {v V e : ℝ} (hx : x.IsFinite) (hv : x.toReal = v)
    (hV : |v| ≤ V) (hcap : V * (7 / 400) + V * (22 / 10000000000) ≤ capF)
    (he : V * (22 / 10000000000) + 1 / 16777216 * (V * (7 / 400) + V * (22 / 10000000000)) +
      1 / 10 ^ 40 ≤ e) :
    B32 (radians_float x) (v * (piD / 180)) e (V * (7 / 400)) := by
  have h := B32.mul (B32.lit hx hv hV) (deg32 hL) (R := V * (7 / 400)) (e := e)
    (by simpa using hcap) (by simpa using he) le_rfl
  exact h

/-- `radians(x)` of a finite `x` of value `0` is a finite `0`. -/
theorem radians_zero (hL : LibmSpec) {x : Float32} (hx : x.IsFinite) (h0 : x.toReal = 0) :
    (radians_float x).IsFinite ∧ (radians_float x).toReal = 0 := by
  have hq := (deg32 hL).1.1
  have := Float32.mul_exact hx hq hx (by rw [h0, zero_mul])
  exact ⟨this.1, this.2.trans h0⟩

/-! ## `ang_vel_limit` with zero limits -/

open AC_AttitudeControl_Multi in
/-- **`ang_vel_limit` with the three limits `0`** (finite floats of value `0`, as the mission's
`ATC_RATE_R_MAX = ATC_RATE_P_MAX = ATC_RATE_Y_MAX = 0` give): the vector is returned unchanged. -/
theorem ang_vel_limit_zero (e : Vector3f.State) {r q y : Float32} (hr : r.IsFinite)
    (hr0 : r.toReal = 0) (hq : q.IsFinite) (hq0 : q.toReal = 0) (hy : y.IsFinite)
    (hy0 : y.toReal = 0) : ang_vel_limit e r q y = e := by
  have zr : is_zero_float r = true := (isZero_iff hr).2 (by rw [hr0]; norm_num)
  have zq : is_zero_float q = true := (isZero_iff hq).2 (by rw [hq0]; norm_num)
  have zy : is_zero_float y = true := (isZero_iff hy).2 (by rw [hy0]; norm_num)
  simp only [ang_vel_limit, Id.run, zr, zq, zy, Bool.true_or, Bool.not_true, Bool.false_eq_true,
    ite_true, ite_false, id_pure_eq]

open AC_AttitudeControl_Multi in
/-- `ang_vel_limit` as `attitude_controller_run_quat` calls it, with `ATC_RATE_*_MAX = 0`. -/
theorem ang_vel_limit_mission (hL : LibmSpec) (p : Params) (e : Vector3f.State)
    (hr : p._ang_vel_roll_max_degs.IsFinite) (hr0 : p._ang_vel_roll_max_degs.toReal = 0)
    (hq : p._ang_vel_pitch_max_degs.IsFinite) (hq0 : p._ang_vel_pitch_max_degs.toReal = 0)
    (hy : p._ang_vel_yaw_max_degs.IsFinite) (hy0 : p._ang_vel_yaw_max_degs.toReal = 0) :
    ang_vel_limit e (radians_float p._ang_vel_roll_max_degs)
      (radians_float p._ang_vel_pitch_max_degs) (radians_float p._ang_vel_yaw_max_degs) = e := by
  obtain ⟨f1, e1⟩ := radians_zero hL hr hr0
  obtain ⟨f2, e2⟩ := radians_zero hL hq hq0
  obtain ⟨f3, e3⟩ := radians_zero hL hy hy0
  exact ang_vel_limit_zero e f1 e1 f2 e2 f3 e3

/-! ## The square-root controller in its linear zone -/

/-- `16 |e|` is a `float` (four exact doublings). -/
theorem exists_sixteen {a : Float32} (ha : a.IsFinite) (hb : |a.toReal| ≤ 2 ^ 20) :
    ∃ d : Float32, d.IsFinite ∧ d.toReal = 16 * a.toReal := by
  have hm : (2 : ℝ) ^ 30 ≤ maxFinite32 := by
    have : (2 : ℝ) ^ 30 ≤ capF := by norm_num [capF]
    linarith [capF_le_max32]
  obtain ⟨d1, f1, e1⟩ := Float32.exists_double ha (by rw [abs_mul]; norm_num; linarith)
  obtain ⟨d2, f2, e2⟩ := Float32.exists_double f1 (by rw [abs_mul, e1, abs_mul]; norm_num; linarith)
  obtain ⟨d3, f3, e3⟩ := Float32.exists_double f2
    (by rw [abs_mul, e2, e1, abs_mul, abs_mul]; norm_num; linarith)
  obtain ⟨d4, f4, e4⟩ := Float32.exists_double f3
    (by rw [abs_mul, e3, e2, e1, abs_mul, abs_mul, abs_mul]; norm_num; linarith)
  exact ⟨d4, f4, by rw [e4, e3, e2, e1]; ring⟩

/-- **`sqrt_controller` in its linear zone**: for `1 ≤ p ≤ 16`, `2⁻²² ≤ lim ≤ 1024`,
`2⁻²³ ≤ dt ≤ 1/16` and `|e| ≤ (lim / p²)(1 - 2⁻²⁰)`, the result is the `float` product `e * p` (the
square-root branches are not taken and the clamp to `±|e| / dt` is inactive). -/
theorem sqrt_ctrl_linear (hL : LibmSpec) {e p lim dt : Float32} (fe : e.IsFinite) (fp : p.IsFinite)
    (fl : lim.IsFinite) (fdt : dt.IsFinite) (hP1 : 1 ≤ p.toReal) (hP16 : p.toReal ≤ 16)
    (hL1 : 2 ^ (-22 : ℤ) ≤ lim.toReal) (hL2 : lim.toReal ≤ 1024)
    (hdt1 : 2 ^ (-23 : ℤ) ≤ dt.toReal) (hdt2 : dt.toReal ≤ 1 / 16)
    (hz : |e.toReal| ≤ lim.toReal / p.toReal ^ 2 * (1 - 1 / 2 ^ 20)) :
    sqrt_controller_float4 e p lim dt = e * p := by
  set P := p.toReal with hPd
  set L := lim.toReal with hLd
  have hL0 : (0 : ℝ) < L := lt_of_lt_of_le (by positivity) hL1
  have h22 : (2 : ℝ) ^ (-22 : ℤ) = 1 / 4194304 := by norm_num
  have h23 : (2 : ℝ) ^ (-23 : ℤ) = 1 / 8388608 := by norm_num
  have h24 : (2 : ℝ) ^ (-24 : ℤ) = 1 / 16777216 := by norm_num
  have h150 : (2 : ℝ) ^ (-150 : ℤ) ≤ 1 / 10 ^ 40 := by
    rw [show (2 : ℝ) ^ (-150 : ℤ) = 1 / 2 ^ 150 by norm_num]; norm_num
  rw [h22] at hL1; rw [h23] at hdt1
  have hmax : (2 : ℝ) ^ 30 ≤ maxFinite32 := by
    have : (2 : ℝ) ^ 30 ≤ capF := by norm_num [capF]
    linarith [capF_le_max32]
  have he1 : |e.toReal| ≤ 1024 := by
    refine hz.trans ?_
    have : L / P ^ 2 ≤ L := div_le_self hL0.le (by nlinarith)
    have : L / P ^ 2 * (1 - 1 / 2 ^ 20) ≤ L / P ^ 2 := by
      have : 0 ≤ L / P ^ 2 := by positivity
      nlinarith
    linarith
  -- the branch conditions
  have hnl : is_negative_float lim = false :=
    Contracts.Track.Att.isNeg_false hL fl (by have : (0 : ℝ) ≤ 2 ^ (-24 : ℤ) := by positivity
                                              linarith)
  have hzl : is_zero_float lim = false := isZero_false fl (by rw [abs_of_pos hL0, h23]; linarith)
  have hzp : is_zero_float p = false :=
    isZero_false fp (by rw [abs_of_pos (by linarith), h23]; linarith)
  have hpos : is_positive_float dt = true := isPos_true fdt (by rw [h23]; linarith)
  -- `p²`
  have hPP : |P * P| ≤ maxFinite32 := by rw [abs_mul, abs_of_pos (by linarith)]; nlinarith
  obtain ⟨fpp, epp⟩ := Float32.mul_err_all fp fp hPP
  rw [h24, abs_of_pos (show (0 : ℝ) < p.toReal * p.toReal by nlinarith)] at epp
  have hpp_lo : P * P / 2 ≤ (p * p).toReal := by
    have := (abs_le.1 epp).1; nlinarith
  have hpp_hi : (p * p).toReal ≤ P ^ 2 * (1 + 1 / 2 ^ 21) := by
    have := (abs_le.1 epp).2; nlinarith
  have hpp0 : 0 < (p * p).toReal := by nlinarith
  -- the linear distance `lim / p²` is at least `|e|`
  have hq : |L / (p * p).toReal| ≤ maxFinite32 := by
    rw [abs_div, abs_of_pos hL0, abs_of_pos hpp0, div_le_iff₀ hpp0]; nlinarith
  obtain ⟨fld, -⟩ := Float32.div_err_all fl fpp hpp0.ne' hq
  have fae : (Float32.abs e).IsFinite := (Float32.isFinite_abs e).2 fe
  have hle : |e.toReal| ≤ L / (p * p).toReal := by
    rw [le_div_iff₀ hpp0]
    calc |e.toReal| * (p * p).toReal ≤ (L / P ^ 2 * (1 - 1 / 2 ^ 20)) * (P ^ 2 * (1 + 1 / 2 ^ 21)) :=
          mul_le_mul hz hpp_hi hpp0.le (by have : 0 ≤ L / P ^ 2 := by positivity
                                           nlinarith)
      _ = L * ((1 - 1 / 2 ^ 20) * (1 + 1 / 2 ^ 21)) := by
          have : P ^ 2 ≠ 0 := by positivity
          field_simp
      _ ≤ L := mul_le_of_le_one_right hL0.le (by norm_num)
  have hld : |e.toReal| ≤ (lim / (p * p)).toReal := by
    have := (Float32.div_bracket fl fpp hpp0.ne' hq fae).1 (by rw [Float32.toReal_abs]; exact hle)
    rwa [Float32.toReal_abs] at this
  have hgt : ¬ (e > lim / sq_float p) := by
    show ¬ (lim / (p * p) < e)
    rw [Float32.lt_iff_toReal_lt fld fe]
    have := le_abs_self e.toReal; linarith
  have hlt : ¬ (e < -(lim / sq_float p)) := by
    show ¬ (e < -(lim / (p * p)))
    rw [Float32.lt_iff_toReal_lt fe ((Float32.isFinite_neg _).2 fld), Float32.toReal_neg]
    have := neg_abs_le e.toReal; linarith
  -- the rate clamp `±|e| / dt` contains `e p`
  have hdt0 : (0 : ℝ) < dt.toReal := by linarith
  obtain ⟨d, fd, ed⟩ := exists_sixteen fae (by rw [Float32.toReal_abs, abs_abs]; linarith)
  rw [Float32.toReal_abs] at ed
  have hEP : |e.toReal * P| ≤ maxFinite32 := by
    rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < P)]; nlinarith [abs_nonneg e.toReal]
  obtain ⟨fc, -⟩ := Float32.mul_err_all fe fp hEP
  have hq2 : |(Float32.abs e).toReal / dt.toReal| ≤ maxFinite32 := by
    rw [Float32.toReal_abs, abs_div, abs_abs, abs_of_pos hdt0, div_le_iff₀ hdt0]
    have h60 : (2 : ℝ) ^ 60 ≤ maxFinite32 := by
      have : (2 : ℝ) ^ 60 ≤ capF := by norm_num [capF]
      linarith [capF_le_max32]
    have : (2 : ℝ) ^ 60 * (1 / 8388608) ≤ maxFinite32 * dt.toReal :=
      mul_le_mul h60 hdt1 (by norm_num) (by linarith)
    norm_num at this; linarith
  have fna : (-(Float32.abs e)).IsFinite := (Float32.isFinite_neg _).2 fae
  have hq3 : |(-(Float32.abs e)).toReal / dt.toReal| ≤ maxFinite32 := by
    rw [Float32.toReal_neg, neg_div, abs_neg]; exact hq2
  obtain ⟨fhi, -⟩ := Float32.div_err_all fae fdt hdt0.ne' hq2
  obtain ⟨flo, -⟩ := Float32.div_err_all fna fdt hdt0.ne' hq3
  have hed : |e.toReal| * 16 ≤ |e.toReal| / dt.toReal := by
    rw [le_div_iff₀ hdt0]; nlinarith [abs_nonneg e.toReal]
  have hEPb : |e.toReal * P| ≤ 16 * |e.toReal| := by
    rw [abs_mul, abs_of_pos (by linarith : (0 : ℝ) < P)]; nlinarith [abs_nonneg e.toReal]
  have c_hi : (e * p).toReal ≤ d.toReal :=
    (Float32.mul_bracket fe fp hEP fd).2 (by rw [ed]; linarith [le_abs_self (e.toReal * P)])
  have d_hi : d.toReal ≤ (Float32.abs e / dt).toReal :=
    (Float32.div_bracket fae fdt hdt0.ne' hq2 fd).1 (by rw [ed, Float32.toReal_abs]; linarith)
  have fnd : (-d).IsFinite := (Float32.isFinite_neg _).2 fd
  have c_lo : (-d).toReal ≤ (e * p).toReal :=
    (Float32.mul_bracket fe fp hEP fnd).1 (by rw [Float32.toReal_neg, ed]; linarith [neg_abs_le (e.toReal * P)])
  have d_lo : (-(Float32.abs e) / dt).toReal ≤ (-d).toReal :=
    (Float32.div_bracket fna fdt hdt0.ne' hq3 fnd).2
      (by rw [Float32.toReal_neg, Float32.toReal_neg, ed, Float32.toReal_abs, neg_div]; linarith)
  have hcon := constrain_inside (Int32.toUInt32 (606 : Int32)) fc flo fhi (d_lo.trans c_lo)
    (c_hi.trans d_hi)
  simp only [sqrt_controller_float4, Id.run, hnl, hzl, hzp, hpos, hgt, hlt, Bool.false_or,
    Bool.false_eq_true, ite_false, ite_true, id_pure_eq, hcon]

/-! ## The second-order limits -/

/-- Roll and pitch: `constrain(radians(1800) / 2, radians(40), radians(720))` is `radians(720)`
(the upper bound is active), of value in `[12.566, 12.567]`; `radians(1800)` is about `31.4`. -/
theorem accel_lim_rp (hL : LibmSpec) {a : Float32} (ha : a.IsFinite) (hav : a.toReal = 1800)
    (line : UInt32) :
    (radians_float a).IsFinite ∧ 31 ≤ (radians_float a).toReal ∧
    (constrain_value_line_float (radians_float a / (2.0 : Float32)) (radians_float (40.0 : Float32))
        (radians_float (720.0 : Float32)) line).IsFinite ∧
    12566 / 1000 ≤ (constrain_value_line_float (radians_float a / (2.0 : Float32))
        (radians_float (40.0 : Float32)) (radians_float (720.0 : Float32)) line).toReal ∧
    (constrain_value_line_float (radians_float a / (2.0 : Float32)) (radians_float (40.0 : Float32))
        (radians_float (720.0 : Float32)) line).toReal ≤ 12567 / 1000 := by
  have r1 : B32 (radians_float a) _ (6 / 1000000) _ :=
    radians_b32 hL ha hav (V := 1800) (by norm_num) (by norm_num [capF]) (by norm_num)
  have b2 : B32 (2.0 : Float32) 2 0 2 := B32.lit f32_isFinite_2p0 f32_toReal_2p0 (by norm_num)
  have am : B32 (radians_float a / (2.0 : Float32)) _ (4 / 1000000) (63 / 4) :=
    B32.div (mlo := 2) r1 b2 (by norm_num) (by norm_num) (by norm_num) (by norm_num [capF])
      (by norm_num)
  have lo : B32 (radians_float (40.0 : Float32)) _ (14 / 100000000) _ :=
    radians_b32 hL f32_isFinite_40p0 f32_toReal_40p0 (V := 40) (by norm_num) (by norm_num [capF])
      (by norm_num)
  have hi : B32 (radians_float (720.0 : Float32)) _ (24 / 10000000) _ :=
    radians_b32 hL f32_isFinite_720p0 f32_toReal_720p0 (V := 720) (by norm_num)
      (by norm_num [capF]) (by norm_num)
  have p1 := (abs_le.1 r1.1.2)
  have p2 := (abs_le.1 am.1.2)
  have p3 := (abs_le.1 lo.1.2)
  have p4 := (abs_le.1 hi.1.2)
  have hpi1 : (31415926 / 10000000 : ℝ) ≤ piD := by norm_num [piD]
  have hpi2 : piD ≤ 31415927 / 10000000 := by norm_num [piD]
  obtain ⟨fc, ec⟩ := constrain_spec line am.1.1 lo.1.1 hi.1.1 (by linarith)
  rw [ec, min_eq_left (by linarith), max_eq_right (by linarith)]
  exact ⟨r1.1.1, by linarith, fc, by linarith, by linarith⟩

/-- Yaw: `constrain(radians(270) / 2, radians(10), radians(120))` is `radians(120)` (the upper
bound is active: `radians(270) / 2 ≈ 2.356`), of value in `[2.0943, 2.0945]`. -/
theorem accel_lim_y (hL : LibmSpec) {a : Float32} (ha : a.IsFinite) (hav : a.toReal = 270)
    (line : UInt32) :
    (radians_float a).IsFinite ∧ 4 ≤ (radians_float a).toReal ∧
    (constrain_value_line_float (radians_float a / (2.0 : Float32)) (radians_float (10.0 : Float32))
        (radians_float (120.0 : Float32)) line).IsFinite ∧
    20943 / 10000 ≤ (constrain_value_line_float (radians_float a / (2.0 : Float32))
        (radians_float (10.0 : Float32)) (radians_float (120.0 : Float32)) line).toReal ∧
    (constrain_value_line_float (radians_float a / (2.0 : Float32)) (radians_float (10.0 : Float32))
        (radians_float (120.0 : Float32)) line).toReal ≤ 20945 / 10000 := by
  have r1 : B32 (radians_float a) _ (9 / 10000000) _ :=
    radians_b32 hL ha hav (V := 270) (by norm_num) (by norm_num [capF]) (by norm_num)
  have b2 : B32 (2.0 : Float32) 2 0 2 := B32.lit f32_isFinite_2p0 f32_toReal_2p0 (by norm_num)
  have am : B32 (radians_float a / (2.0 : Float32)) _ (6 / 10000000) (189 / 80) :=
    B32.div (mlo := 2) r1 b2 (by norm_num) (by norm_num) (by norm_num) (by norm_num [capF])
      (by norm_num)
  have lo : B32 (radians_float (10.0 : Float32)) _ (4 / 100000000) _ :=
    radians_b32 hL f32_isFinite_10p0 f32_toReal_10p0 (V := 10) (by norm_num) (by norm_num [capF])
      (by norm_num)
  have hi : B32 (radians_float (120.0 : Float32)) _ (4 / 10000000) _ :=
    radians_b32 hL f32_isFinite_120p0 f32_toReal_120p0 (V := 120) (by norm_num)
      (by norm_num [capF]) (by norm_num)
  have p1 := (abs_le.1 r1.1.2)
  have p2 := (abs_le.1 am.1.2)
  have p3 := (abs_le.1 lo.1.2)
  have p4 := (abs_le.1 hi.1.2)
  have hpi1 : (31415926 / 10000000 : ℝ) ≤ piD := by norm_num [piD]
  have hpi2 : piD ≤ 31415927 / 10000000 := by norm_num [piD]
  obtain ⟨fc, ec⟩ := constrain_spec line am.1.1 lo.1.1 hi.1.1 (by linarith)
  rw [ec, min_eq_left (by linarith), max_eq_right (by linarith)]
  exact ⟨r1.1.1, by linarith, fc, by linarith, by linarith⟩

/-! ## The angle P controller -/

/-- One rounded product `e * p` with `|p e| ≤ 3/2`: within `10⁻⁷` of `p e`. -/
theorem mul_near {e p : Float32} {K : ℝ} (fe : e.IsFinite) (fp : p.IsFinite) (hpv : p.toReal = K)
    (hb : |K * e.toReal| ≤ 3 / 2) : A32 (e * p) (K * e.toReal) (1 / 10000000) := by
  have hm : |e.toReal * p.toReal| ≤ maxFinite32 := by
    rw [hpv, mul_comm]; have : (3 / 2 : ℝ) ≤ capF := by norm_num [capF]
    linarith [capF_le_max32]
  obtain ⟨f, er⟩ := Float32.mul_err_all fe fp hm
  refine ⟨f, ?_⟩
  rw [hpv, mul_comm e.toReal K] at er
  have h150 : (2 : ℝ) ^ (-150 : ℤ) ≤ 1 / 10 ^ 40 := by
    rw [show (2 : ℝ) ^ (-150 : ℤ) = 1 / 2 ^ 150 by norm_num]; norm_num
  have h24 : (2 : ℝ) ^ (-24 : ℤ) = 1 / 16777216 := by norm_num
  rw [h24] at er
  linarith

open AC_AttitudeControl_Multi in
/-- **C10, the angle P controller** (`update_ang_vel_target_from_att_error`) with the mission's
parameters (`ATC_ANG_*_P = 9, 9, 4.5`, `ATC_ACCEL_*_MAX = 1800, 1800, 270 deg/s²`, square-root
controller on, angle-P scale `1`, `dt = 1/400`), in the linear zones `|e.x|, |e.y| ≤ 0.155`,
`|e.z| ≤ 0.1034`: each component is the `float` product of the error and the gain, within `10⁻⁷`
of `(9 e.x, 9 e.y, 4.5 e.z)`. -/
theorem ang_vel_target_spec (hL : LibmSpec) (p : Params) (s : State) (err : Vector3f.State)
    (hkr : p._p_angle_roll._kp.IsFinite) (hkrv : p._p_angle_roll._kp.toReal = 9)
    (hkp : p._p_angle_pitch._kp.IsFinite) (hkpv : p._p_angle_pitch._kp.toReal = 9)
    (hky : p._p_angle_yaw._kp.IsFinite) (hkyv : p._p_angle_yaw._kp.toReal = 9 / 2)
    (hsc : Ones s._angle_P_scale)
    (har : p._accel_roll_max_degss.IsFinite) (harv : p._accel_roll_max_degss.toReal = 1800)
    (hap : p._accel_pitch_max_degss.IsFinite) (hapv : p._accel_pitch_max_degss.toReal = 1800)
    (hay : p._accel_yaw_max_degss.IsFinite) (hayv : p._accel_yaw_max_degss.toReal = 270)
    (huse : s._use_sqrt_controller = true) (hdt : s._dt_s.IsFinite) (hdtv : s._dt_s.toReal = dtR)
    (fx : err.x.IsFinite) (fy : err.y.IsFinite) (fz : err.z.IsFinite)
    (hx : |err.x.toReal| ≤ 155 / 1000) (hy : |err.y.toReal| ≤ 155 / 1000)
    (hz : |err.z.toReal| ≤ 1034 / 10000) :
    let r := update_ang_vel_target_from_att_error p s err
    r.x = err.x * (p._p_angle_roll._kp * s._angle_P_scale.x) ∧
      r.y = err.y * (p._p_angle_pitch._kp * s._angle_P_scale.y) ∧
      r.z = err.z * (p._p_angle_yaw._kp * s._angle_P_scale.z) ∧
      A32 r.x (9 * err.x.toReal) (1 / 10000000) ∧ A32 r.y (9 * err.y.toReal) (1 / 10000000) ∧
      A32 r.z (9 / 2 * err.z.toReal) (1 / 10000000) := by
  intro r
  obtain ⟨sx, sxv, sy, syv, sz, szv⟩ := hsc
  obtain ⟨kxf, kxv⟩ := mul_one_val hkr sx sxv
  obtain ⟨kyf, kyv⟩ := mul_one_val hkp sy syv
  obtain ⟨kzf, kzv⟩ := mul_one_val hky sz szv
  rw [hkrv] at kxv; rw [hkpv] at kyv; rw [hkyv] at kzv
  obtain ⟨arf, arv, lrf, lr1, lr2⟩ := accel_lim_rp hL har harv (Int32.toUInt32 (1352 : Int32))
  obtain ⟨apf, apv, lpf, lp1, lp2⟩ := accel_lim_rp hL hap hapv (Int32.toUInt32 (1360 : Int32))
  obtain ⟨ayf, ayv, lyf, ly1, ly2⟩ := accel_lim_y hL hay hayv (Int32.toUInt32 (1368 : Int32))
  have gr : get_accel_roll_max_radss p = radians_float p._accel_roll_max_degss := rfl
  have zr : is_zero_float (radians_float p._accel_roll_max_degss) = false :=
    isZero_false arf (by rw [abs_of_pos (by linarith)]; norm_num; linarith)
  have gp : get_accel_pitch_max_radss p = radians_float p._accel_pitch_max_degss := rfl
  have zp : is_zero_float (radians_float p._accel_pitch_max_degss) = false :=
    isZero_false apf (by rw [abs_of_pos (by linarith)]; norm_num; linarith)
  have gy : get_accel_yaw_max_radss p = radians_float p._accel_yaw_max_degss := rfl
  have zy : is_zero_float (radians_float p._accel_yaw_max_degss) = false :=
    isZero_false ayf (by rw [abs_of_pos (by linarith)]; norm_num; linarith)
  have d1 : (2 : ℝ) ^ (-23 : ℤ) ≤ s._dt_s.toReal := by rw [hdtv]; norm_num
  have d2 : s._dt_s.toReal ≤ 1 / 16 := by rw [hdtv]; norm_num
  have ex : sqrt_controller_float4 err.x (p._p_angle_roll._kp * s._angle_P_scale.x)
      (constrain_value_line_float (radians_float p._accel_roll_max_degss / (2.0 : Float32))
        (radians_float (40.0 : Float32)) (radians_float (720.0 : Float32))
        (Int32.toUInt32 (1352 : Int32))) s._dt_s =
      err.x * (p._p_angle_roll._kp * s._angle_P_scale.x) :=
    sqrt_ctrl_linear hL fx kxf lrf hdt (by rw [kxv]; norm_num) (by rw [kxv]; norm_num)
      (by norm_num; linarith) (by linarith) d1 d2 (by rw [kxv]; norm_num; linarith)
  have ey : sqrt_controller_float4 err.y (p._p_angle_pitch._kp * s._angle_P_scale.y)
      (constrain_value_line_float (radians_float p._accel_pitch_max_degss / (2.0 : Float32))
        (radians_float (40.0 : Float32)) (radians_float (720.0 : Float32))
        (Int32.toUInt32 (1360 : Int32))) s._dt_s =
      err.y * (p._p_angle_pitch._kp * s._angle_P_scale.y) :=
    sqrt_ctrl_linear hL fy kyf lpf hdt (by rw [kyv]; norm_num) (by rw [kyv]; norm_num)
      (by norm_num; linarith) (by linarith) d1 d2 (by rw [kyv]; norm_num; linarith)
  have ez : sqrt_controller_float4 err.z (p._p_angle_yaw._kp * s._angle_P_scale.z)
      (constrain_value_line_float (radians_float p._accel_yaw_max_degss / (2.0 : Float32))
        (radians_float (10.0 : Float32)) (radians_float (120.0 : Float32))
        (Int32.toUInt32 (1368 : Int32))) s._dt_s =
      err.z * (p._p_angle_yaw._kp * s._angle_P_scale.z) :=
    sqrt_ctrl_linear hL fz kzf lyf hdt (by rw [kzv]; norm_num) (by rw [kzv]; norm_num)
      (by norm_num; linarith) (by linarith) d1 d2 (by rw [kzv]; norm_num; linarith)
  have e1 : r.x = err.x * (p._p_angle_roll._kp * s._angle_P_scale.x) := by
    simp only [r, update_ang_vel_target_from_att_error, Id.run, huse, gr, gp, gy, zr, zp, zy, Bool.not_false,
      Bool.true_and, ite_true, id_pure_eq, ex, ey, ez]
  have e2 : r.y = err.y * (p._p_angle_pitch._kp * s._angle_P_scale.y) := by
    simp only [r, update_ang_vel_target_from_att_error, Id.run, huse, gr, gp, gy, zr, zp, zy, Bool.not_false,
      Bool.true_and, ite_true, id_pure_eq, ex, ey, ez]
  have e3 : r.z = err.z * (p._p_angle_yaw._kp * s._angle_P_scale.z) := by
    simp only [r, update_ang_vel_target_from_att_error, Id.run, huse, gr, gp, gy, zr, zp, zy, Bool.not_false,
      Bool.true_and, ite_true, id_pure_eq, ex, ey, ez]
  refine ⟨e1, e2, e3, ?_, ?_, ?_⟩
  · rw [e1]; exact mul_near fx kxf kxv (by rw [abs_mul]; norm_num; linarith)
  · rw [e2]; exact mul_near fy kyf kyv (by rw [abs_mul]; norm_num; linarith)
  · rw [e3]; exact mul_near fz kzf kzv (by rw [abs_mul]; norm_num; linarith)

/-! ## The branch of `attitude_controller_run_quat` -/

/-- `radians(30)` is within `10⁻⁷` of `piD / 6`; `radians(30) * 2` is finite, above `1`. -/
theorem rad30 (hL : LibmSpec) :
    A32 (radians_float (30.0 : Float32)) (30 * (piD / 180)) (1 / 10000000) ∧
      (radians_float (30.0 : Float32) * (2.0 : Float32)).IsFinite ∧
      1 ≤ (radians_float (30.0 : Float32) * (2.0 : Float32)).toReal := by
  have r : B32 (radians_float (30.0 : Float32)) _ (1 / 10000000) _ :=
    radians_b32 hL f32_isFinite_30p0 f32_toReal_30p0 (V := 30) (by norm_num) (by norm_num [capF])
      (by norm_num)
  have b2 : B32 (2.0 : Float32) 2 0 2 := B32.lit f32_isFinite_2p0 f32_toReal_2p0 (by norm_num)
  have m : B32 _ _ (1 / 1000000) _ := B32.mul r b2 (R := 21 / 20) (by norm_num [capF]) (by norm_num)
    (by norm_num)
  have := (abs_le.1 m.1.2)
  have hpi1 : (31415926 / 10000000 : ℝ) ≤ piD := by norm_num [piD]
  exact ⟨r.1, m.1.1, by linarith⟩

open AC_AttitudeControl_Multi in
/-- **C10, the composition in `attitude_controller_run_quat`**: with `th` the result of
`thrust_heading_rotation_angles` (new attitude target, attitude error, thrust angle, thrust error
angle), when the thrust error angle is a finite value at most `0.5235` (below `radians(30)`), the
new body-rate target `_ang_vel_body_rads` is the `float` sum (`Vector3f::operator+=`) of the angle-P
output after `ang_vel_limit` and the feed-forward `ang_vel_body_feedforward`, and
`_feedforward_scalar = 1`. -/
theorem attitude_run_quat_eq (hL : LibmSpec) (p : Params) (s : State) (inp : Inputs) :
    let qb := inp.get_quat_body_to_ned_q
    let th := thrust_heading_rotation_angles p s._attitude_target qb Vector3f.init_void
      s._thrust_angle_rad s._thrust_error_angle_rad
    let s1 : State :=
      { s with _attitude_target := th.1, _thrust_angle_rad := (th.2.2).1,
               _thrust_error_angle_rad := (th.2.2).2 }
    let av := ang_vel_limit (update_ang_vel_target_from_att_error p s1 (th.2).1)
      (radians_float p._ang_vel_roll_max_degs) (radians_float p._ang_vel_pitch_max_degs)
      (radians_float p._ang_vel_yaw_max_degs)
    let ff := Quaternion.op_mul_Vector3f
      (Quaternion.op_mul_Quaternion (Quaternion.inverse qb) th.1) s._ang_vel_target_rads
    (th.2.2).2.IsFinite → (th.2.2).2.toReal ≤ 5235 / 10000 →
    (attitude_controller_run_quat p s inp)._ang_vel_body_rads = (Vector3f.op_add_assign av ff).1 ∧
      (attitude_controller_run_quat p s inp)._feedforward_scalar = (1.0 : Float32) := by
  intro qb th s1 av ff hf hle
  obtain ⟨r30, f60, v60⟩ := rad30 hL
  have hpi1 : (31415926 / 10000000 : ℝ) ≤ piD := by norm_num [piD]
  have h1 : ¬ ((th.2.2).2 > radians_float (30.0 : Float32) * (2.0 : Float32)) := by
    show ¬ (_ < _)
    rw [Float32.lt_iff_toReal_lt f60 hf]; linarith
  have h2 : ¬ ((th.2.2).2 > radians_float (30.0 : Float32)) := by
    show ¬ (_ < _)
    rw [Float32.lt_iff_toReal_lt r30.1 hf]
    have := (abs_le.1 r30.2).1; linarith
  simp only [th, qb] at h1 h2
  simp only [attitude_controller_run_quat, Id.run, id_pure_eq, h1, h2, ite_false]
  exact ⟨rfl, trivial⟩

open AC_AttitudeControl_Multi in
/-- **C10, the angle loop** (`attitude_controller_run_quat` with the mission's parameters): when
the thrust error angle is at most `0.5235` and the attitude error `err` returned by
`thrust_heading_rotation_angles` is in the linear zones (`|err.x|, |err.y| ≤ 0.155`,
`|err.z| ≤ 0.1034`), the new body-rate target is, per component, the `float` sum of the angle-P
output (the `float` product of the error and the gain, within `10⁻⁷` of `9 err.x`, `9 err.y`,
`4.5 err.z`) and the feed-forward `ff`; `ang_vel_limit` (`ATC_RATE_*_MAX = 0`) changes nothing. -/
theorem attitude_run_quat_spec (hL : LibmSpec) (p : Params) (s : State) (inp : Inputs)
    (hkr : p._p_angle_roll._kp.IsFinite) (hkrv : p._p_angle_roll._kp.toReal = 9)
    (hkp : p._p_angle_pitch._kp.IsFinite) (hkpv : p._p_angle_pitch._kp.toReal = 9)
    (hky : p._p_angle_yaw._kp.IsFinite) (hkyv : p._p_angle_yaw._kp.toReal = 9 / 2)
    (hsc : Ones s._angle_P_scale)
    (har : p._accel_roll_max_degss.IsFinite) (harv : p._accel_roll_max_degss.toReal = 1800)
    (hap : p._accel_pitch_max_degss.IsFinite) (hapv : p._accel_pitch_max_degss.toReal = 1800)
    (hay : p._accel_yaw_max_degss.IsFinite) (hayv : p._accel_yaw_max_degss.toReal = 270)
    (hvr : p._ang_vel_roll_max_degs.IsFinite) (hvrv : p._ang_vel_roll_max_degs.toReal = 0)
    (hvp : p._ang_vel_pitch_max_degs.IsFinite) (hvpv : p._ang_vel_pitch_max_degs.toReal = 0)
    (hvy : p._ang_vel_yaw_max_degs.IsFinite) (hvyv : p._ang_vel_yaw_max_degs.toReal = 0)
    (huse : s._use_sqrt_controller = true) (hdt : s._dt_s.IsFinite) (hdtv : s._dt_s.toReal = dtR) :
    let qb := inp.get_quat_body_to_ned_q
    let th := thrust_heading_rotation_angles p s._attitude_target qb Vector3f.init_void
      s._thrust_angle_rad s._thrust_error_angle_rad
    let err := (th.2).1
    let ff := Quaternion.op_mul_Vector3f
      (Quaternion.op_mul_Quaternion (Quaternion.inverse qb) th.1) s._ang_vel_target_rads
    (th.2.2).2.IsFinite → (th.2.2).2.toReal ≤ 5235 / 10000 →
    err.x.IsFinite → err.y.IsFinite → err.z.IsFinite →
    |err.x.toReal| ≤ 155 / 1000 → |err.y.toReal| ≤ 155 / 1000 → |err.z.toReal| ≤ 1034 / 10000 →
    let r := (attitude_controller_run_quat p s inp)._ang_vel_body_rads
    r.x = err.x * (p._p_angle_roll._kp * s._angle_P_scale.x) + ff.x ∧
      r.y = err.y * (p._p_angle_pitch._kp * s._angle_P_scale.y) + ff.y ∧
      r.z = err.z * (p._p_angle_yaw._kp * s._angle_P_scale.z) + ff.z ∧
      A32 (err.x * (p._p_angle_roll._kp * s._angle_P_scale.x)) (9 * err.x.toReal) (1 / 10000000) ∧
      A32 (err.y * (p._p_angle_pitch._kp * s._angle_P_scale.y)) (9 * err.y.toReal) (1 / 10000000) ∧
      A32 (err.z * (p._p_angle_yaw._kp * s._angle_P_scale.z)) (9 / 2 * err.z.toReal)
        (1 / 10000000) := by
  intro qb th err ff hf hle fx fy fz bx by' bz r
  obtain ⟨eq, -⟩ := attitude_run_quat_eq hL p s inp hf hle
  let s1 : State :=
    { s with _attitude_target := th.1, _thrust_angle_rad := (th.2.2).1,
             _thrust_error_angle_rad := (th.2.2).2 }
  obtain ⟨e1, e2, e3, a1, a2, a3⟩ := ang_vel_target_spec hL p s1 err hkr hkrv hkp hkpv hky hkyv
    hsc har harv hap hapv hay hayv huse hdt hdtv fx fy fz bx by' bz
  have hlim := ang_vel_limit_mission hL p (update_ang_vel_target_from_att_error p s1 err)
    hvr hvrv hvp hvpv hvy hvyv
  have hr : r = (Vector3f.op_add_assign (update_ang_vel_target_from_att_error p s1 err) ff).1 := by
    rw [← hlim]; exact eq
  refine ⟨?_, ?_, ?_, e1 ▸ a1, e2 ▸ a2, e3 ▸ a3⟩
  · rw [hr]; exact congrArg (· + ff.x) e1
  · rw [hr]; exact congrArg (· + ff.y) e2
  · rw [hr]; exact congrArg (· + ff.z) e3

end

end Contracts.Track.Att
