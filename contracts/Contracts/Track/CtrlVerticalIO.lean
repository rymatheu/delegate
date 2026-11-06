import Contracts.Track.CtrlVerticalPID
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

/-!
# C1, C7, C12 (throttle filter): the estimates, the angle boost and the 2 Hz throttle filter

* `estimates` (C1): `update_estimates` stores the sample exactly;
* `set_throttle_out_eq`, `boost_A32` (C7): `set_throttle_out(thr, true, 2)` hands the motors
  `thr / cos θ_T` (the attitude controller's target thrust angle), within `2⁻¹⁸ |thr|`, for
  `cos_pitch · cos_roll ≥ 0.11` and `|θ_T| ≤ 1`;
* `utf_eq`, `throttle_filter` (C12): the throttle filter's step `f + αT (u - f)`, clamps inactive.

`A32.lpf` is the bound of `A32.filt` for the operand order of `DigitalLPF::_apply`.
`throttle_filter2` (exact coefficient under `PiF32`) and `boost_c` (the tilt bound `cos θ ≥ c0`
as a parameter) are the sharp forms the tick uses.
-/

namespace Contracts.Track.CtrlV

open Float.Model UnpackedFloat Contracts.Mission

noncomputable section

set_option linter.unusedSimpArgs false

theorem cvl_att : @AC_Attitude_lib.constrain_value_line_float =
    @AC_PosControl_lib.constrain_value_line_float := rfl
theorem cvl_mot : @AP_Motors_lib.constrain_value_line_float =
    @AC_PosControl_lib.constrain_value_line_float := rfl
theorem alpha_mot : @AP_Motors_lib.calc_lowpass_alpha_dt =
    @AC_PosControl_lib.calc_lowpass_alpha_dt := rfl

/-- `1 / b` for `b` within `2⁻²²` of `rb ∈ [1/2, 1]`: within `2⁻¹⁹` of `1 / rb`. -/
theorem A32.recip {b : Float32} {rb eb : ℝ} (hb : A32 b rb eb) (hrb : 1 / 2 ≤ rb) (hrb1 : rb ≤ 1)
    (heb : eb ≤ 1 / 2 ^ 22) : A32 ((1.0 : Float32) / b) (1 / rb) (1 / 2 ^ 19) := by
  have hη1 := η32_small; have hη0 := η32_pos
  obtain ⟨hbf, hbe⟩ := hb
  set B := b.toReal with hBd
  have hB : 1 / 2 - 1 / 2 ^ 22 ≤ B := by rw [abs_le] at hbe; linarith
  have hB1 : B ≤ 1 + 1 / 2 ^ 22 := by rw [abs_le] at hbe; linarith
  have hB0 : 0 < B := by linarith
  have hq : |1 / B| ≤ 3 := by
    rw [abs_of_pos (by positivity), div_le_iff₀ hB0]; linarith
  obtain ⟨hf, he⟩ := Float32.div_err_all Float32.isFinite_lit_one hbf (by linarith)
    (by rw [Float32.toReal_lit_one]; exact hq.trans (by linarith [capF_le_max32, show (3 : ℝ) ≤ capF by norm_num [capF]]))
  rw [Float32.toReal_lit_one] at he
  refine ⟨hf, ?_⟩
  have h1 : |1 / B - 1 / rb| ≤ 5 / 2 ^ 22 := by
    rw [div_sub_div _ _ hB0.ne' (by linarith), abs_div, abs_mul, abs_of_pos hB0,
      abs_of_pos (by linarith : (0 : ℝ) < rb), one_mul, mul_one, div_le_iff₀ (by positivity)]
    have : |rb - B| ≤ eb := by rw [abs_sub_comm]; exact hbe
    nlinarith
  have h2 := abs_sub_le ((1.0 : Float32) / b).toReal (1 / B) (1 / rb)
  have h3 : 2 ^ (-24 : ℤ) * |1 / B| + 2 ^ (-150 : ℤ) ≤ 3 / 2 ^ 24 + 1 / 2 ^ 140 := by
    have : (2 : ℝ) ^ (-24 : ℤ) = 1 / 2 ^ 24 := by norm_num
    have h150 : (2 : ℝ) ^ (-150 : ℤ) ≤ 1 / 2 ^ 140 := by
      rw [show (2 : ℝ) ^ (-150 : ℤ) = 1 / 2 ^ 150 by norm_num]; norm_num
    rw [this]; nlinarith
  have := he.trans h3
  norm_num at this h1 h2 ⊢
  linarith

/-- **The low-pass step of `LowPassFilter::apply`**, `o + (x - o) α` (the operand order of
`DigitalLPF::_apply`): the bound of `A32.filt`. -/
theorem A32.lpf {e x α : Float32} {xr αr ex δα M : ℝ} (he : e.IsFinite) (hx : A32 x xr ex)
    (hα : A32 α αr δα) (hα0 : 0 ≤ αr) (hα1 : αr ≤ 1) (hδ : δα ≤ 1 / 2 ^ 20)
    (hexM : ex ≤ M) (hxM : |xr| ≤ M) (heM : |e.toReal| ≤ M) (hMc : M ≤ 2 ^ 90) :
    A32 (e + (x - e) * α) (e.toReal + αr * (xr - e.toReal))
      (αr * ex + (4 * δα + (1 + 12 * αr) * u32) * M + 2 * η32) := by
  have hη1 := η32_small; have hη0 := η32_pos
  have hu : u32 = 1 / 16777216 := u32_eq
  have hδ0 : 0 ≤ δα := (abs_nonneg _).trans hα.2
  have hex0 : 0 ≤ ex := (abs_nonneg _).trans hx.2
  have hM0 : 0 ≤ M := (abs_nonneg _).trans heM
  have mf : (2 : ℝ) ^ 100 ≤ maxFinite32 := capF_le_max32
  -- the difference
  set X := x.toReal - e.toReal with hXd
  have hxx : |x.toReal - xr| ≤ ex := hx.2
  have hX : |X| ≤ 3 * M := by
    have h1 := abs_sub x.toReal e.toReal
    have h2 : |x.toReal| ≤ |xr| + ex := hx.abs_le
    linarith
  obtain ⟨f1, e1⟩ := Float32.sub_err_all hx.1 he (by linarith)
  set D := (x - e).toReal with hDd
  have e1' : |D - X| ≤ u32 * (3 * M) := by
    rw [show (2 : ℝ) ^ (-24 : ℤ) = u32 from rfl] at e1
    exact e1.trans (mul_le_mul_of_nonneg_left hX u32_pos.le)
  have hD : |D| ≤ 4 * M := by
    have := abs_sub_abs_le_abs_sub D X; rw [hu] at e1'; linarith
  -- the coefficient
  have hαa : |α.toReal| ≤ αr + δα := by
    have := hα.abs_le; rwa [abs_of_nonneg hα0] at this
  have hαD : |α.toReal * D| ≤ (αr + δα) * (4 * M) := by
    rw [abs_mul]; exact mul_le_mul hαa hD (abs_nonneg _) (by linarith)
  obtain ⟨f2, e2⟩ := Float32.mul_err_all f1 hα.1 (by rw [mul_comm]; nlinarith)
  set P := ((x - e) * α).toReal with hPd
  have e2' : |P - α.toReal * D| ≤ u32 * ((αr + δα) * (4 * M)) + η32 := by
    have := rnd32 e2
    rw [mul_comm D α.toReal] at this
    nlinarith [u32_pos]
  have hP : |P| ≤ (αr + δα) * (4 * M) * (1 + u32) + η32 := by
    have := abs_sub_abs_le_abs_sub P (α.toReal * D); nlinarith [u32_pos]
  -- the sum
  have hEP : |e.toReal + P| ≤ M + (αr + δα) * (4 * M) * (1 + u32) + η32 :=
    (abs_add_le _ _).trans (by linarith)
  have hb16 : (αr + δα) * (4 * M) * (1 + u32) ≤ 16 * M := by
    have : αr + δα ≤ 2 := by linarith
    have : 1 + u32 ≤ 2 := by rw [hu]; norm_num
    have : (αr + δα) * (4 * M) ≤ 2 * (4 * M) := mul_le_mul_of_nonneg_right (by linarith) (by linarith)
    have := mul_le_mul this (show 1 + u32 ≤ 2 by linarith) (by rw [hu]; norm_num) (by linarith)
    linarith
  obtain ⟨f3, e3⟩ := Float32.add_err_all he f2 (by linarith)
  refine ⟨f3, ?_⟩
  have e3' : |(e + (x - e) * α).toReal - (e.toReal + P)| ≤
      u32 * (M + (αr + δα) * (4 * M) * (1 + u32) + η32) :=
    e3.trans (mul_le_mul_of_nonneg_left hEP u32_pos.le)
  -- the pieces of the error
  have k1 : |α.toReal * D - α.toReal * X| ≤ (αr + δα) * (u32 * (3 * M)) := by
    rw [← mul_sub, abs_mul]; exact mul_le_mul hαa e1' (abs_nonneg _) (by linarith)
  have k2 : |α.toReal * X - αr * X| ≤ δα * (3 * M) := by
    rw [← sub_mul, abs_mul]; exact mul_le_mul hα.2 hX (abs_nonneg _) hδ0
  have k3 : |αr * X - αr * (xr - e.toReal)| ≤ αr * ex := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hα0]
    exact mul_le_mul_of_nonneg_left (by rw [hXd, show x.toReal - e.toReal - (xr - e.toReal) = x.toReal - xr by ring]; exact hxx) hα0
  have tri : |(e + (x - e) * α).toReal - (e.toReal + αr * (xr - e.toReal))| ≤
      |(e + (x - e) * α).toReal - (e.toReal + P)| + |P - α.toReal * D| +
        |α.toReal * D - α.toReal * X| + |α.toReal * X - αr * X| +
        |αr * X - αr * (xr - e.toReal)| := by
    have a1 := abs_sub_le (e + (x - e) * α).toReal (e.toReal + P) (e.toReal + αr * (xr - e.toReal))
    have a2 := abs_sub_le (e.toReal + P) (e.toReal + α.toReal * D) (e.toReal + αr * (xr - e.toReal))
    have a3 := abs_sub_le (e.toReal + α.toReal * D) (e.toReal + α.toReal * X) (e.toReal + αr * (xr - e.toReal))
    have a4 := abs_sub_le (e.toReal + α.toReal * X) (e.toReal + αr * X) (e.toReal + αr * (xr - e.toReal))
    simp only [add_sub_add_left_eq_sub] at a1 a2 a3 a4
    linarith
  refine tri.trans ?_
  rw [hu] at e2' e3' k1 ⊢
  have := mul_nonneg hδ0 hM0; have := mul_nonneg hα0 hM0
  have := mul_nonneg (mul_nonneg hα0 hM0) hδ0
  have := mul_nonneg (mul_nonneg hδ0 hM0) hδ0
  ring_nf at e2' e3' k1 k2 k3 ⊢
  linarith


/-! ## C7: `AC_AttitudeControl_Multi::set_throttle_out` with the angle boost -/

section Att
open AC_Attitude_lib AC_AttitudeControl_Multi

theorem althold_thrust_angle (p : Params) (s : State) (inp : Inputs) (t : Float32) :
    (update_althold_lean_angle_max p s inp t)._thrust_angle_rad = s._thrust_angle_rad := by
  unfold update_althold_lean_angle_max
  simp only [Id.run]
  split <;> rfl

/-- The motors' throttle that `set_throttle_out(thr, true, 2)` writes, as a float expression:
`thr · inverted_factor · boost_factor` with the attitude state's `_thrust_angle_rad`. -/
theorem set_throttle_out_eq (p : Params) (s : State) (o : Outputs) (inp : Inputs) (t c : Float32)
    (hen : p._angle_boost_enabled ≠ 0) :
    (set_throttle_out p s o inp t true c).2.set_throttle =
      t * constrain_value_line_float ((10.0 : Float32) * (inp.cos_pitch * inp.cos_roll)) 0.0 1.0
          (Int32.toUInt32 398) *
        ((1.0 : Float32) / constrain_value_line_float (Float32.cos s._thrust_angle_rad)
          (0.100000001 : Float32) 1.0 (Int32.toUInt32 400)) ∧
    (set_throttle_out p s o inp t true c).2.set_throttle_filter_cutoff = c := by
  have hen' : (p._angle_boost_enabled != 0) = true := by simpa using hen
  refine ⟨?_, rfl⟩
  simp only [set_throttle_out, get_throttle_boosted, Id.run, hen', Bool.not_true,
    Bool.false_eq_true, ite_false, ite_true]
  rw [althold_thrust_angle]
  rfl


/-- **C7, the angle boost.** With the vehicle's `cos_pitch · cos_roll ≥ 0.11` (the inverted factor
is `1`) and the target thrust angle `|θ| ≤ 1` rad (`cos θ ≥ 1/2`, the boost clamp `[0.1, 1]`
inactive), the throttle `set_throttle_out(thr, true, ·)` hands the motors is `thr / cos θ` within
`2⁻¹⁸ |thr| + η` (`cosf` within `2⁻²²`, `LibmSpec`), for any `|thr| ≤ 2²⁰`. -/
theorem boost_A32 (hL : LibmSpec) {t cp cr θ : Float32} (ht : t.IsFinite) (htb : |t.toReal| ≤ 2 ^ 20)
    (hcp : cp.IsFinite) (hcr : cr.IsFinite) (hcpb : |cp.toReal| ≤ 1) (hcrb : |cr.toReal| ≤ 1)
    (hct : 11 / 100 ≤ cp.toReal * cr.toReal) (hθ : θ.IsFinite) (hθb : |θ.toReal| ≤ 1) :
    A32 (t * constrain_value_line_float ((10.0 : Float32) * (cp * cr)) 0.0 1.0 (Int32.toUInt32 398) *
        ((1.0 : Float32) / constrain_value_line_float (Float32.cos θ) (0.100000001 : Float32) 1.0
          (Int32.toUInt32 400)))
      (t.toReal / Real.cos θ.toReal) (1 / 2 ^ 18 * |t.toReal| + η32) := by
  have hη1 := η32_small; have hη0 := η32_pos
  have hu : u32 = 1 / 16777216 := u32_eq
  -- the inverted factor is `1`
  have h10 : (10.0 : Float32).IsFinite ∧ (10.0 : Float32).toReal = 10 :=
    ⟨f32_isFinite_10p0, f32_toReal_10p0⟩
  have c1 := (A32.of_exact hcp).mul (A32.of_exact hcr) (by
    simp only [mul_zero, zero_mul, add_zero, abs_zero]; rw [abs_mul]; norm_num [capF]; nlinarith [abs_nonneg cp.toReal, abs_nonneg cr.toReal])
  simp only [mul_zero, zero_mul, add_zero, abs_zero, zero_add] at c1
  have hcc : |cp.toReal * cr.toReal| ≤ 1 := by
    rw [abs_mul]; nlinarith [abs_nonneg cp.toReal, abs_nonneg cr.toReal]
  have c2 := ((A32.of_exact h10.1).congr h10.2).mul c1 (by
    simp only [mul_zero, zero_mul, add_zero, abs_zero]; rw [hu]; norm_num [capF]; rw [abs_mul] at hcc
    nlinarith [abs_nonneg cp.toReal, abs_nonneg cr.toReal])
  have hc2 : 1 ≤ ((10.0 : Float32) * (cp * cr)).toReal := by
    have h := c2.2
    rw [abs_le] at h
    have h3 := c1.2
    rw [hu] at h h3
    norm_num at h h3
    rw [abs_le] at hcc
    nlinarith [abs_nonneg cp.toReal, abs_nonneg cr.toReal, abs_le.1 (show |(cp * cr).toReal - cp.toReal * cr.toReal| ≤ _ from h3)]
  obtain ⟨fi, ei⟩ := constrain_spec (Int32.toUInt32 398) c2.1 Float32.isFinite_lit_zero
    Float32.isFinite_lit_one (by simp)
  rw [← cvl_att] at fi ei
  rw [Float32.toReal_lit_zero, Float32.toReal_lit_one, min_eq_left hc2, max_eq_right zero_le_one] at ei
  obtain ⟨t1f, t1v⟩ := f32_mul_one ht fi ei
  -- the boost factor `1 / cos θ`
  obtain ⟨cf, cb, ce⟩ := hL.cosf θ hθ
  have hcos : 1 / 2 ≤ Real.cos θ.toReal := by
    have := Real.one_sub_sq_div_two_le_cos (x := θ.toReal)
    have : θ.toReal ^ 2 ≤ 1 := by rw [← sq_abs]; nlinarith [abs_nonneg θ.toReal]
    linarith
  have hlib : libm32Err = 1 / 4194304 := by rw [libm32Err]; norm_num
  rw [hlib] at ce
  have hc0 : (0.100000001 : Float32).toReal ≤ (Float32.cos θ).toReal := by
    have : (0.100000001 : Float32).toReal ≤ 1 / 8 := by
      rw [show (0.100000001 : Float32).toReal = 13421773 / 134217728 by
        rw [Float32.toReal_of_unpack (by f32_unpack : (0.100000001 : Float32).toModel.unpack =
          .finite .positive 13421773 (-27) (by decide))]; simp [Sign.apply]; norm_num]
      norm_num
    rw [abs_le] at ce; linarith
  have hc1 : (Float32.cos θ).toReal ≤ (1.0 : Float32).toReal := by
    rw [Float32.toReal_lit_one]; exact (le_abs_self _).trans cb
  have h01 : (0.100000001 : Float32).IsFinite :=
    Float32.isFinite_of_unpack (by f32_unpack : (0.100000001 : Float32).toModel.unpack =
          .finite .positive 13421773 (-27) (by decide))
  obtain ⟨fc, ec⟩ := constrain_spec (Int32.toUInt32 400) cf h01 Float32.isFinite_lit_one
    (hc0.trans hc1)
  rw [← cvl_att] at fc ec
  rw [min_eq_right hc1, max_eq_right hc0] at ec
  have ac : A32 (constrain_value_line_float (Float32.cos θ) (0.100000001 : Float32) 1.0
      (Int32.toUInt32 400)) (Real.cos θ.toReal) (1 / 4194304) := ⟨fc, by rw [ec]; exact ce⟩
  have hcle : Real.cos θ.toReal ≤ 1 := Real.cos_le_one _
  have ab' := A32.recip ac hcos hcle (by norm_num)
  -- the product
  have t1 : A32 (t * constrain_value_line_float ((10.0 : Float32) * (cp * cr)) 0.0 1.0
      (Int32.toUInt32 398)) t.toReal 0 := ⟨t1f, by rw [t1v]; simp⟩
  have hq : 1 / Real.cos θ.toReal ≤ 2 := by rw [div_le_iff₀ (by linarith)]; linarith
  have hq0 : 0 < 1 / Real.cos θ.toReal := by positivity
  rw [show t.toReal / Real.cos θ.toReal = t.toReal * (1 / Real.cos θ.toReal) by ring]
  generalize 1 / Real.cos θ.toReal = q at *
  have pr := t1.mul ab' (by
    simp only [mul_zero, zero_mul, add_zero, zero_add]
    rw [abs_mul, abs_of_pos hq0]; norm_num [capF]; nlinarith [abs_nonneg t.toReal])
  refine pr.mono ?_
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [u32_eq, abs_mul, abs_of_pos hq0]
  have := abs_nonneg t.toReal
  have : |t.toReal| * q ≤ 2 * |t.toReal| := by nlinarith
  nlinarith

end Att

/-! ## C12 (first half): the 2 Hz throttle filter, `AP_MotorsMulticopter::update_throttle_filter` -/

section Motors
open AP_Motors_lib AP_MotorsMatrix

theorem utf_eq (s : State) (inp : Inputs) (harm : s._armed = true)
    (hin : s._throttle_filter.initialised = true)
    (h0 : ¬ (s._throttle_filter.output + (s._throttle_in - s._throttle_filter.output) *
      calc_lowpass_alpha_dt s._dt_s s._throttle_filter.cutoff_freq < 0.0))
    (h1 : ¬ (s._throttle_filter.output + (s._throttle_in - s._throttle_filter.output) *
      calc_lowpass_alpha_dt s._dt_s s._throttle_filter.cutoff_freq > 1.0)) :
    (update_throttle_filter s inp)._throttle_filter.output =
      s._throttle_filter.output + (s._throttle_in - s._throttle_filter.output) *
        calc_lowpass_alpha_dt s._dt_s s._throttle_filter.cutoff_freq := by
  unfold update_throttle_filter
  simp only [armed_void, Id.run, harm, ite_true, LowPassFilterFloat.apply, LowPassFilterFloat._apply,
    hin, Bool.not_true, Bool.false_eq_true, ite_false, LowPassFilterFloat.get, id_pure_eq,
    id_bind_eq]
  simp only [h0, h1, ite_false]
  split <;> rfl

/-- **C12, the throttle filter.** Armed, initialised, with the cutoff `2` Hz, the period `0.0025f`,
and the filter and `_throttle_in` in `[1/4, 3/4]` (D8): the filter's new output is
`f + αT (u - f)` within `18 u + 2 η`, and the clamps to `[0, 1]` are inactive. -/
theorem throttle_filter (hL : LibmSpec) (s : State) (inp : Inputs) (harm : s._armed = true)
    (hin : s._throttle_filter.initialised = true) (hdt : s._dt_s.IsFinite) (hdtv : s._dt_s.toReal = dtR)
    (hc : s._throttle_filter.cutoff_freq.IsFinite) (hcv : s._throttle_filter.cutoff_freq.toReal = 2)
    (hf : s._throttle_filter.output.IsFinite) (hu : s._throttle_in.IsFinite)
    (hf0 : 1 / 4 ≤ s._throttle_filter.output.toReal) (hf1 : s._throttle_filter.output.toReal ≤ 3 / 4)
    (hu0 : 1 / 4 ≤ s._throttle_in.toReal) (hu1 : s._throttle_in.toReal ≤ 3 / 4) :
    A32 (update_throttle_filter s inp)._throttle_filter.output
      (s._throttle_filter.output.toReal + (16352567 / 536870912 : ℝ) *
        (s._throttle_in.toReal - s._throttle_filter.output.toReal)) (18 * u32 + 2 * η32) := by
  have hη1 := η32_small; have hη0 := η32_pos
  have hα : A32 (calc_lowpass_alpha_dt s._dt_s s._throttle_filter.cutoff_freq)
      (16352567 / 536870912) (1 / 2 ^ 22) := by
    rw [alpha_mot]; exact alpha2 hL hdt hdtv hc hcv
  have h := A32.lpf (M := 1) hf (A32.of_exact hu) hα (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by rw [abs_le]; constructor <;> linarith) (by rw [abs_le]; constructor <;> linarith)
    (by norm_num)
  have h' := h.mono (e' := 18 * u32 + 2 * η32) (by rw [u32_eq]; norm_num)
  have hb := h'.2
  rw [abs_le, u32_eq] at hb
  have h0 : ¬ (s._throttle_filter.output + (s._throttle_in - s._throttle_filter.output) *
      calc_lowpass_alpha_dt s._dt_s s._throttle_filter.cutoff_freq < 0.0) := by
    rw [Float32.lt_iff_toReal_lt h'.1 Float32.isFinite_lit_zero, Float32.toReal_lit_zero, not_lt]
    nlinarith
  have h1 : ¬ (s._throttle_filter.output + (s._throttle_in - s._throttle_filter.output) *
      calc_lowpass_alpha_dt s._dt_s s._throttle_filter.cutoff_freq > 1.0) := by
    rw [gt_iff_lt, Float32.lt_iff_toReal_lt Float32.isFinite_lit_one h'.1, Float32.toReal_lit_one,
      not_lt]
    nlinarith
  rw [utf_eq s inp harm hin h0 h1]
  exact h'

end Motors

/-! ## Sharp forms: the throttle filter with the exact coefficient, the boost with a tilt bound -/

section Motors2
open AP_Motors_lib AP_MotorsMatrix

/-- `αT` as a real. -/
def αTr : ℝ := 16352567 / 536870912

/-- **C12, the throttle filter, sharp form**: with the coefficient exact (`PiF32`), the period
`0.0025f` and the cutoff `2.0f` of `set_throttle_out`. -/
theorem throttle_filter2 (hL : LibmSpec) (hpi : PiF32) (s : State) (inp : Inputs)
    (harm : s._armed = true) (hin : s._throttle_filter.initialised = true) (hdt : s._dt_s = d0)
    (hc : s._throttle_filter.cutoff_freq = 2.0)
    (hf : s._throttle_filter.output.IsFinite) (hu : s._throttle_in.IsFinite)
    (hf0 : 1 / 4 ≤ s._throttle_filter.output.toReal) (hf1 : s._throttle_filter.output.toReal ≤ 3 / 4)
    (hu0 : 1 / 4 ≤ s._throttle_in.toReal) (hu1 : s._throttle_in.toReal ≤ 3 / 4) :
    A32 (update_throttle_filter s inp)._throttle_filter.output
      (s._throttle_filter.output.toReal + αTr * (s._throttle_in.toReal - s._throttle_filter.output.toReal))
      ((102 / 100 + 411 / 100 * αTr) * u32 * (3 / 4) + 2 * η32) := by
  have hη1 := η32_small; have hη0 := η32_pos
  have hα : A32 (calc_lowpass_alpha_dt s._dt_s s._throttle_filter.cutoff_freq) αTr 0 := by
    rw [alpha_mot, hdt, hc]; exact alphaT hL hpi
  have h := A32.lpf2 (M := 3 / 4) hf (A32.of_exact hu) hα (by rw [αTr]; norm_num)
    (by rw [αTr]; norm_num) (by norm_num) (by norm_num)
    (by rw [abs_le]; constructor <;> linarith) (by rw [abs_le]; constructor <;> linarith) (by norm_num)
  have h' : A32 (s._throttle_filter.output + (s._throttle_in - s._throttle_filter.output) *
      calc_lowpass_alpha_dt s._dt_s s._throttle_filter.cutoff_freq)
      (s._throttle_filter.output.toReal + αTr * (s._throttle_in.toReal - s._throttle_filter.output.toReal))
      ((102 / 100 + 411 / 100 * αTr) * u32 * (3 / 4) + 2 * η32) :=
    h.mono (le_of_eq (by ring))
  have hb := h'.2
  have hc2 : (102 / 100 + 411 / 100 * αTr) * u32 * (3 / 4) + 2 * η32 ≤ 1 / 100 := by
    rw [αTr, u32_eq]; nlinarith
  have hcv : |s._throttle_filter.output.toReal + αTr * (s._throttle_in.toReal - s._throttle_filter.output.toReal) - 1 / 2| ≤ 1 / 4 := by
    rw [abs_le]; rw [αTr]; constructor <;> nlinarith
  have h0 : ¬ (s._throttle_filter.output + (s._throttle_in - s._throttle_filter.output) *
      calc_lowpass_alpha_dt s._dt_s s._throttle_filter.cutoff_freq < 0.0) := by
    rw [Float32.lt_iff_toReal_lt h'.1 Float32.isFinite_lit_zero, Float32.toReal_lit_zero, not_lt]
    rw [abs_le] at hb hcv; linarith
  have h1 : ¬ (s._throttle_filter.output + (s._throttle_in - s._throttle_filter.output) *
      calc_lowpass_alpha_dt s._dt_s s._throttle_filter.cutoff_freq > 1.0) := by
    rw [gt_iff_lt, Float32.lt_iff_toReal_lt Float32.isFinite_lit_one h'.1, Float32.toReal_lit_one,
      not_lt]
    rw [abs_le] at hb hcv; linarith
  rw [utf_eq s inp harm hin h0 h1]
  exact h'

/-- `1 / b` for `b` within `eb ≤ 2⁻²²` of `rb ∈ [c0, 1]`, `c0 ≥ 1/2`: within
`eb / ((c0 - eb) c0) + u / (c0 - eb) + η` of `1 / rb`. -/
theorem A32.recip2 {b : Float32} {rb eb c0 : ℝ} (hb : A32 b rb eb) (hc0 : 1 / 2 ≤ c0) (hrb : c0 ≤ rb)
    (hrb1 : rb ≤ 1) (heb : eb ≤ 1 / 2 ^ 22) :
    A32 ((1.0 : Float32) / b) (1 / rb) (eb / ((c0 - eb) * c0) + u32 / (c0 - eb) + η32) := by
  have hη1 := η32_small; have hη0 := η32_pos
  obtain ⟨hbf, hbe⟩ := hb
  have heb0 : 0 ≤ eb := (abs_nonneg _).trans hbe
  set B := b.toReal with hBd
  have hB : c0 - eb ≤ B := by rw [abs_le] at hbe; linarith
  have hce : 0 < c0 - eb := by linarith
  have hB0 : 0 < B := by linarith
  have hq : |1 / B| ≤ 1 / (c0 - eb) := by
    rw [abs_of_pos (by positivity)]; exact one_div_le_one_div_of_le hce hB
  have hq3 : 1 / (c0 - eb) ≤ 3 := by
    rw [div_le_iff₀ hce]; linarith
  obtain ⟨hf, he⟩ := Float32.div_err_all Float32.isFinite_lit_one hbf (by linarith)
    (by rw [Float32.toReal_lit_one]; exact hq.trans (hq3.trans (by linarith [capF_le_max32, show (3 : ℝ) ≤ capF by norm_num [capF]])))
  rw [Float32.toReal_lit_one] at he
  refine ⟨hf, ?_⟩
  have h1 : |1 / B - 1 / rb| ≤ eb / ((c0 - eb) * c0) := by
    rw [div_sub_div _ _ hB0.ne' (by linarith), abs_div, abs_mul, abs_of_pos hB0,
      abs_of_pos (by linarith : (0 : ℝ) < rb), one_mul, mul_one]
    have hrbB : |rb - B| ≤ eb := by rw [abs_sub_comm]; exact hbe
    have hpos1 : 0 < B * rb := mul_pos hB0 (by linarith)
    have hpos2 : 0 < (c0 - eb) * c0 := mul_pos hce (by linarith)
    rw [div_le_div_iff₀ hpos1 hpos2]
    have h4 : (c0 - eb) * c0 ≤ B * rb := mul_le_mul hB hrb (by linarith) (by linarith)
    have h5 : |rb - B| * ((c0 - eb) * c0) ≤ eb * ((c0 - eb) * c0) :=
      mul_le_mul_of_nonneg_right hrbB hpos2.le
    have h6 : eb * ((c0 - eb) * c0) ≤ eb * (B * rb) := mul_le_mul_of_nonneg_left h4 heb0
    linarith
  have h2 := abs_sub_le ((1.0 : Float32) / b).toReal (1 / B) (1 / rb)
  have he' := rnd32 he
  rw [← hBd] at he'
  have h3 : u32 * |1 / B| ≤ u32 / (c0 - eb) := by
    have := mul_le_mul_of_nonneg_left hq u32_pos.le
    rwa [mul_one_div] at this
  linarith

/-- **C7, the angle boost, with the tilt bound as a parameter**: for `cos θ ≥ c0 ≥ 1/2`, the
throttle `thr / cos θ` within `(2⁻²² / ((c0 - 2⁻²²) c0) + 3 u / (c0 - 2⁻²²) + η) |thr| + η`. -/
theorem boost_c (hL : LibmSpec) {t cp cr θ : Float32} {c0 : ℝ} (ht : t.IsFinite)
    (htb : |t.toReal| ≤ 2 ^ 20)
    (hcp : cp.IsFinite) (hcr : cr.IsFinite) (hcpb : |cp.toReal| ≤ 1) (hcrb : |cr.toReal| ≤ 1)
    (hct : 11 / 100 ≤ cp.toReal * cr.toReal) (hθ : θ.IsFinite) (hc0 : 1 / 2 ≤ c0)
    (hcθ : c0 ≤ Real.cos θ.toReal) :
    A32 (t * AC_Attitude_lib.constrain_value_line_float ((10.0 : Float32) * (cp * cr)) 0.0 1.0
        (Int32.toUInt32 398) *
        ((1.0 : Float32) / AC_Attitude_lib.constrain_value_line_float (Float32.cos θ)
          (0.100000001 : Float32) 1.0 (Int32.toUInt32 400)))
      (t.toReal / Real.cos θ.toReal)
      ((1 / 2 ^ 22 / ((c0 - 1 / 2 ^ 22) * c0) + 3 * u32 / (c0 - 1 / 2 ^ 22) + η32) * |t.toReal| +
        η32) := by
  have hη1 := η32_small; have hη0 := η32_pos
  have hu : u32 = 1 / 16777216 := u32_eq
  -- the inverted factor is `1` (as in `boost_A32`)
  have h10 : (10.0 : Float32).IsFinite ∧ (10.0 : Float32).toReal = 10 :=
    ⟨f32_isFinite_10p0, f32_toReal_10p0⟩
  have c1 := (A32.of_exact hcp).mul (A32.of_exact hcr) (by
    simp only [mul_zero, zero_mul, add_zero, abs_zero]; rw [abs_mul]; norm_num [capF]; nlinarith [abs_nonneg cp.toReal, abs_nonneg cr.toReal])
  simp only [mul_zero, zero_mul, add_zero, abs_zero, zero_add] at c1
  have hcc : |cp.toReal * cr.toReal| ≤ 1 := by
    rw [abs_mul]; nlinarith [abs_nonneg cp.toReal, abs_nonneg cr.toReal]
  have c2 := ((A32.of_exact h10.1).congr h10.2).mul c1 (by
    simp only [mul_zero, zero_mul, add_zero, abs_zero]; rw [hu]; norm_num [capF]; rw [abs_mul] at hcc
    nlinarith [abs_nonneg cp.toReal, abs_nonneg cr.toReal])
  have hc2 : 1 ≤ ((10.0 : Float32) * (cp * cr)).toReal := by
    have h := c2.2
    rw [abs_le] at h
    have h3 := c1.2
    rw [hu] at h h3
    norm_num at h h3
    rw [abs_le] at hcc
    nlinarith [abs_nonneg cp.toReal, abs_nonneg cr.toReal, abs_le.1 (show |(cp * cr).toReal - cp.toReal * cr.toReal| ≤ _ from h3)]
  obtain ⟨fi, ei⟩ := constrain_spec (Int32.toUInt32 398) c2.1 Float32.isFinite_lit_zero
    Float32.isFinite_lit_one (by simp)
  rw [← cvl_att] at fi ei
  rw [Float32.toReal_lit_zero, Float32.toReal_lit_one, min_eq_left hc2, max_eq_right zero_le_one] at ei
  obtain ⟨t1f, t1v⟩ := f32_mul_one ht fi ei
  -- the boost factor
  obtain ⟨cf, cb, ce⟩ := hL.cosf θ hθ
  have hlib : libm32Err = 1 / 4194304 := by rw [libm32Err]; norm_num
  rw [hlib] at ce
  have hc0' : (0.100000001 : Float32).toReal ≤ (Float32.cos θ).toReal := by
    have : (0.100000001 : Float32).toReal ≤ 1 / 8 := by
      rw [show (0.100000001 : Float32).toReal = 13421773 / 134217728 by
        rw [Float32.toReal_of_unpack (by f32_unpack : (0.100000001 : Float32).toModel.unpack =
          .finite .positive 13421773 (-27) (by decide))]; simp [Sign.apply]; norm_num]
      norm_num
    rw [abs_le] at ce; linarith
  have hc1 : (Float32.cos θ).toReal ≤ (1.0 : Float32).toReal := by
    rw [Float32.toReal_lit_one]; exact (le_abs_self _).trans cb
  have h01 : (0.100000001 : Float32).IsFinite :=
    Float32.isFinite_of_unpack (by f32_unpack : (0.100000001 : Float32).toModel.unpack =
          .finite .positive 13421773 (-27) (by decide))
  obtain ⟨fc, ec⟩ := constrain_spec (Int32.toUInt32 400) cf h01 Float32.isFinite_lit_one
    (hc0'.trans hc1)
  rw [← cvl_att] at fc ec
  rw [min_eq_right hc1, max_eq_right hc0'] at ec
  have ac : A32 (AC_Attitude_lib.constrain_value_line_float (Float32.cos θ) (0.100000001 : Float32) 1.0
      (Int32.toUInt32 400)) (Real.cos θ.toReal) (1 / 4194304) := ⟨fc, by rw [ec]; exact ce⟩
  have hcle : Real.cos θ.toReal ≤ 1 := Real.cos_le_one _
  have ab := A32.recip2 ac hc0 hcθ hcle (by norm_num)
  -- the product
  have t1 : A32 (t * AC_Attitude_lib.constrain_value_line_float ((10.0 : Float32) * (cp * cr)) 0.0 1.0
      (Int32.toUInt32 398)) t.toReal 0 := ⟨t1f, by rw [t1v]; simp⟩
  have hcθ0 : 0 < Real.cos θ.toReal := by linarith
  have hce : 0 < c0 - 1 / 4194304 := by linarith
  have hq : 1 / Real.cos θ.toReal ≤ 1 / c0 := one_div_le_one_div_of_le (by linarith) hcθ
  have hq2 : 1 / c0 ≤ 1 / (c0 - 1 / 4194304) :=
    one_div_le_one_div_of_le hce (by norm_num)
  have hq0 : 0 < 1 / Real.cos θ.toReal := by positivity
  have hq3 : 1 / (c0 - 1 / 4194304) ≤ 3 := by rw [div_le_iff₀ hce]; linarith
  set E := 1 / 4194304 / ((c0 - 1 / 4194304) * c0) + u32 / (c0 - 1 / 4194304) + η32 with hEd
  have hpc : 0 < (c0 - 1 / 4194304) * c0 := mul_pos hce (by linarith)
  have hE0 : 0 ≤ E := by
    rw [hEd]; have := div_pos (by norm_num : (0:ℝ) < 1 / 4194304) hpc
    have := div_pos u32_pos hce; linarith [η32_pos]
  have hE1 : E ≤ 1 := by
    rw [hEd, u32_eq]
    have h1 : 1 / 4194304 / ((c0 - 1 / 4194304) * c0) ≤ 1 / 1000 := by
      rw [div_le_iff₀ hpc]; nlinarith
    have h2 : 1 / 16777216 / (c0 - 1 / 4194304) ≤ 1 / 1000 := by
      rw [div_le_iff₀ hce]; nlinarith
    linarith
  rw [show t.toReal / Real.cos θ.toReal = t.toReal * (1 / Real.cos θ.toReal) by ring]
  have hab : A32 ((1.0 : Float32) / AC_Attitude_lib.constrain_value_line_float (Float32.cos θ)
      (0.100000001 : Float32) 1.0 (Int32.toUInt32 400)) (1 / Real.cos θ.toReal) E := by
    rw [hEd]; convert ab using 2
  have pr := t1.mul hab (by
    simp only [mul_zero, zero_mul, add_zero, zero_add]
    rw [abs_mul, abs_of_pos hq0]
    have ht0 := abs_nonneg t.toReal
    have h1 : |t.toReal| * (1 / Real.cos θ.toReal) ≤ 2 ^ 20 * 3 :=
      mul_le_mul htb (by linarith) hq0.le (by norm_num)
    have h2 : |t.toReal| * E ≤ 2 ^ 20 * 1 := mul_le_mul htb hE1 hE0 (by norm_num)
    have : (2 : ℝ) ^ 20 * 3 + 2 ^ 20 * 1 ≤ capF := by norm_num [capF]
    linarith)
  refine pr.mono ?_
  simp only [mul_zero, zero_mul, add_zero, zero_add]
  rw [abs_mul, abs_of_pos hq0]
  have ht0 := abs_nonneg t.toReal
  have e1 : |t.toReal| * E = (1 / 4194304 / ((c0 - 1 / 4194304) * c0)) * |t.toReal| +
      (u32 / (c0 - 1 / 4194304)) * |t.toReal| + η32 * |t.toReal| := by rw [hEd]; ring
  have e2 : u32 * (|t.toReal| * (1 / Real.cos θ.toReal) + |t.toReal| * E) ≤
      (u32 / (c0 - 1 / 4194304)) * |t.toReal| + u32 * |t.toReal| * E := by
    have h1 : |t.toReal| * (1 / Real.cos θ.toReal) ≤ |t.toReal| * (1 / (c0 - 1 / 4194304)) :=
      mul_le_mul_of_nonneg_left (hq.trans hq2) ht0
    have h2 := mul_le_mul_of_nonneg_left h1 u32_pos.le
    have e3 : u32 * (|t.toReal| * (1 / (c0 - 1 / 4194304))) = (u32 / (c0 - 1 / 4194304)) * |t.toReal| := by ring
    have e4 : u32 * (|t.toReal| * (1 / Real.cos θ.toReal) + |t.toReal| * E) =
      u32 * (|t.toReal| * (1 / Real.cos θ.toReal)) + u32 * |t.toReal| * E := by ring
    linarith
  have e4 : u32 * |t.toReal| * E ≤ u32 * |t.toReal| := by
    have := mul_le_mul_of_nonneg_left hE1 (mul_nonneg u32_pos.le ht0); linarith
  have e5 : u32 * |t.toReal| ≤ (u32 / (c0 - 1 / 4194304)) * |t.toReal| := by
    apply mul_le_mul_of_nonneg_right _ ht0
    rw [le_div_iff₀ hce]; have := u32_pos; nlinarith
  rw [show (1 : ℝ) / 2 ^ 22 = 1 / 4194304 by norm_num]
  have e9 : (1 / 4194304 / ((c0 - 1 / 4194304) * c0) + 3 * u32 / (c0 - 1 / 4194304) + η32) * |t.toReal| + η32 =
      (1 / 4194304 / ((c0 - 1 / 4194304) * c0)) * |t.toReal| +
      (u32 / (c0 - 1 / 4194304)) * |t.toReal| + η32 * |t.toReal| +
      (u32 / (c0 - 1 / 4194304)) * |t.toReal| + (u32 / (c0 - 1 / 4194304)) * |t.toReal| + η32 := by ring
  rw [e9]
  have k1 := e4.trans e5
  generalize u32 * (|t.toReal| * (1 / Real.cos θ.toReal) + |t.toReal| * E) = X at e2 ⊢
  generalize |t.toReal| * E = Y at e1 e2 ⊢
  generalize u32 * |t.toReal| * E = Z at e2 k1
  linarith

end Motors2

/-! ## C1: `AC_PosControl::update_estimates` -/

/-- **C1.** The estimates are the sample through the port, exactly: `update_estimates` on the
vehicle's inputs (position and velocity always available, no high vibration) stores the sample's
position (double) and velocity (float). -/
theorem estimates (w : Vehicle.World) (s : AC_PosControl_lib.AC_PosControl.State) :
    (AC_PosControl_lib.AC_PosControl.update_estimates s (Vehicle.posInputs w) false)._pos_estimate_ned_m =
        w.sample.pos ∧
      (AC_PosControl_lib.AC_PosControl.update_estimates s (Vehicle.posInputs w) false)._vel_estimate_ned_ms =
        w.sample.vel := by
  constructor <;> rfl

end

end Contracts.Track.CtrlV
