import Contracts.Track.CtrlAttitudeBase
import FloatModel.Lit

/-!
# C11: the rate loop of the attitude controller in `float` (milestone M4)

The translated `AC_PID::update_all` (`AC_PID.cpp:196-311`) and
`AC_AttitudeControl_Multi::rate_controller_run` (`AC_AttitudeControl_Multi.cpp:456-491`) read as
the ideal real PID law plus an explicit rounding budget, with the mission's rate gains
(`ATC_RAT_RLL/PIT_*`, `ATC_RAT_YAW_*`) and the loop period `dt = 1/400` (the `float`
`5368709 / 2³¹`).

* `alpha20`, `alpha2p5`, `alpha0`: the filter coefficient `calc_lowpass_alpha_dt dt f` for
  `f = 20 Hz` (within `2⁻²³` of `16042859 / 2²⁶`), `f = 2.5 Hz` (within `2⁻²⁵` of
  `10143117 / 2²⁸`) and `f = 0` (exactly `1`);
* `modifier_snd`: `SlewLimiter::modifier` returns the factor `1` for every state and input when
  `slew_rate_max = 0`;
* `update_all_eq`, `update_all_reset_eq`: the result of `update_all` (the filter branch and the
  first-tick branch) as explicit `float` expressions;
* `pid_num`: the error budget of those expressions against the ideal law (`pidT`, `pidE`, `pidD`,
  `pidI`, `pidOut`) on the region `|target|, |meas|, |T| ≤ 8`, `|E| ≤ 16`, `|D| ≤ 16384`,
  `|I| ≤ 1/2` (a region the ideal law maps into itself: `ideal_region`);
* `update_all_spec`: the two together, for any gains in the mission's ranges; `roll_pid_spec`,
  `yaw_pid_spec`: the mission's roll/pitch and yaw gains;
* `rate_controller_spec`: the composition: the three outputs handed to the mixer are the three
  PID outputs (`+ sysid = 0`), the three PID states are those of `update_all`, the feed-forward
  outputs are `0`.
-/

namespace Contracts.Track.Att

open Float.Model UnpackedFloat Contracts.Mission AC_Attitude_lib

noncomputable section

/-! ## Small tools -/

theorem a32_shift {x : Float32} {r q e δ : ℝ} (h : A32 x r e) (hq : |r - q| ≤ δ) :
    A32 x q (e + δ) :=
  ⟨h.1, by
    calc |x.toReal - q| ≤ |x.toReal - r| + |r - q| := abs_sub_le _ _ _
      _ ≤ e + δ := add_le_add h.2 hq⟩

theorem B32.lit {x : Float32} {v R : ℝ} (hx : x.IsFinite) (hv : x.toReal = v) (hR : |v| ≤ R) :
    B32 x v 0 R := (B32.of_exact hx (hv ▸ hR)).congr hv

theorem b32_congr_x {x y : Float32} {r e R : ℝ} (h : B32 x r e R) (hy : y.IsFinite)
    (hv : y.toReal = x.toReal) : B32 y r e R := ⟨A32.congr_x h.1 hy hv, h.2⟩

/-- Multiplying by a `float` whose value is `1` is exact. -/
theorem mul_one_val {a b : Float32} (ha : a.IsFinite) (hb : b.IsFinite) (hb1 : b.toReal = 1) :
    (a * b).IsFinite ∧ (a * b).toReal = a.toReal :=
  Float32.mul_exact ha hb ha (by rw [hb1, mul_one])

theorem b32_mul_one {a b : Float32} {r e R : ℝ} (h : B32 a r e R) (hb : b.IsFinite)
    (hb1 : b.toReal = 1) : B32 (a * b) r e R :=
  b32_congr_x h (mul_one_val h.1.1 hb hb1).1 (mul_one_val h.1.1 hb hb1).2

/-- A convex combination stays in a symmetric interval. -/
theorem convex_abs_le {x y a B : ℝ} (hx : |x| ≤ B) (hy : |y| ≤ B) (ha0 : 0 ≤ a) (ha1 : a ≤ 1) :
    |x + a * (y - x)| ≤ B := by
  have e : x + a * (y - x) = (1 - a) * x + a * y := by ring
  rw [e]
  calc |(1 - a) * x + a * y| ≤ |(1 - a) * x| + |a * y| := abs_add_le _ _
    _ = (1 - a) * |x| + a * |y| := by
        rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - a), abs_of_nonneg ha0]
    _ ≤ (1 - a) * B + a * B := by gcongr
    _ = B := by ring

/-- The clamp to `[-c, c]` is `1`-Lipschitz. -/
theorem clamp_lip (c x r : ℝ) : |max (-c) (min c x) - max (-c) (min c r)| ≤ |x - r| := by
  have h1 := abs_max_sub_max_le_abs (min c x) (min c r) (-c)
  rw [max_comm (min c x), max_comm (min c r)] at h1
  have h2 : |min c x - min c r| ≤ |x - r| := by
    rw [min_comm c x, min_comm c r]; exact abs_min_sub_min_le_max x c r c |>.trans (by simp)
  exact h1.trans h2

/-! ## The filter coefficients -/

/-- The loop period: the `float` `1.0f / 400.0f`. -/
abbrev dtR : ℝ := 5368709 / 2147483648

/-- The coefficient of the 20 Hz filters (`FLTT`, `FLTD`) at 400 Hz: the `float` the code computes. -/
abbrev α20 : ℝ := 16042859 / 67108864

/-- The coefficient of the 2.5 Hz yaw error filter (`ATC_RAT_YAW_FLTE`). -/
abbrev α2p5 : ℝ := 10143117 / 268435456

/-- `calc_lowpass_alpha_dt dt 20` with `dt = 1/400`: within `2⁻²³` of `α20`. -/
theorem alpha20 (hL : LibmSpec) {dt c : Float32} (hdt : dt.IsFinite) (hdtv : dt.toReal = dtR)
    (hc : c.IsFinite) (hcv : c.toReal = 20) :
    A32 (calc_lowpass_alpha_dt dt c) α20 (1 / 2 ^ 23) := by
  have hnd : is_negative_float dt = false :=
    Contracts.Track.Att.isNeg_false hL hdt (by rw [hdtv]; norm_num)
  have hnc : is_negative_float c = false :=
    Contracts.Track.Att.isNeg_false hL hc (by rw [hcv]; norm_num)
  have hzc : is_zero_float c = false := isZero_false hc (by rw [hcv]; norm_num)
  have hzd : is_zero_float dt = false := isZero_false hdt (by rw [hdtv]; norm_num)
  simp only [calc_lowpass_alpha_dt, Id.run, hnd, hnc, hzc, hzd, Bool.or_false,
    Bool.false_eq_true, ite_false, id_pure_eq]
  have hpi := pi32 hL
  have bpi : B32 (Float.toFloat32 (3.1415926535897931 : Float)) piD (19 / 100000000) (315 / 100) :=
    ⟨hpi.mono (by rw [u32_eq, η32_eq]; norm_num [piD]),
      by rw [abs_of_pos (by norm_num [piD])]; norm_num [piD]⟩
  have b2 : B32 (Int32.toFloat32 (2 : Int32)) 2 0 2 :=
    B32.lit Float32.isFinite_int32_two Float32.toReal_int32_two (by norm_num)
  have bc : B32 c 20 0 20 := B32.lit hc hcv (by norm_num)
  have bd : B32 dt dtR 0 dtR := B32.lit hdt hdtv (by norm_num)
  have b1 : B32 (1.0 : Float32) 1 0 1 := B32.lit f32_isFinite_1p0 f32_toReal_1p0 (by norm_num)
  have m1 : B32 _ _ (19 / 25000000) (63 / 10) :=
    B32.mul bpi b2 (by norm_num [capF]) (by norm_num) (by norm_num)
  have m2 : B32 _ _ (23 / 1000000) 126 :=
    B32.mul m1 bc (by norm_num [capF]) (by norm_num) (by norm_num)
  have rc : B32 _ _ (1 / 500000000) (199 / 25000) := B32.div (mlo := 125663 / 1000) b1 m2
    (by rw [abs_of_pos (by norm_num [piD])]; norm_num [piD]) (by norm_num) (by norm_num)
    (by norm_num [capF]) (by norm_num)
  have sm : B32 _ _ (27 / 10000000000) (21 / 2000) :=
    B32.add bd rc (by norm_num) (by norm_num [capF]) (by norm_num)
  have q : B32 _ _ (77 / 1000000000) (6 / 25) := B32.div (mlo := 104577 / 10000000) bd sm
    (by rw [abs_of_pos (by norm_num [piD])]; norm_num [piD]) (by norm_num) (by norm_num)
    (by norm_num [capF]) (by norm_num)
  refine (a32_shift q.1 (δ := 1 / 10 ^ 8) ?_).mono (by norm_num)
  rw [abs_le]; constructor <;> norm_num [piD]

/-- `calc_lowpass_alpha_dt dt 2.5` with `dt = 1/400`: within `2⁻²⁵` of `α2p5`. -/
theorem alpha2p5 (hL : LibmSpec) {dt c : Float32} (hdt : dt.IsFinite) (hdtv : dt.toReal = dtR)
    (hc : c.IsFinite) (hcv : c.toReal = 5 / 2) :
    A32 (calc_lowpass_alpha_dt dt c) α2p5 (1 / 2 ^ 25) := by
  have hnd : is_negative_float dt = false :=
    Contracts.Track.Att.isNeg_false hL hdt (by rw [hdtv]; norm_num)
  have hnc : is_negative_float c = false :=
    Contracts.Track.Att.isNeg_false hL hc (by rw [hcv]; norm_num)
  have hzc : is_zero_float c = false := isZero_false hc (by rw [hcv]; norm_num)
  have hzd : is_zero_float dt = false := isZero_false hdt (by rw [hdtv]; norm_num)
  simp only [calc_lowpass_alpha_dt, Id.run, hnd, hnc, hzc, hzd, Bool.or_false,
    Bool.false_eq_true, ite_false, id_pure_eq]
  have hpi := pi32 hL
  have bpi : B32 (Float.toFloat32 (3.1415926535897931 : Float)) piD (19 / 100000000) (315 / 100) :=
    ⟨hpi.mono (by rw [u32_eq, η32_eq]; norm_num [piD]),
      by rw [abs_of_pos (by norm_num [piD])]; norm_num [piD]⟩
  have b2 : B32 (Int32.toFloat32 (2 : Int32)) 2 0 2 :=
    B32.lit Float32.isFinite_int32_two Float32.toReal_int32_two (by norm_num)
  have bc : B32 c (5 / 2) 0 (5 / 2) := B32.lit hc hcv (by norm_num)
  have bd : B32 dt dtR 0 dtR := B32.lit hdt hdtv (by norm_num)
  have b1 : B32 (1.0 : Float32) 1 0 1 := B32.lit f32_isFinite_1p0 f32_toReal_1p0 (by norm_num)
  have m1 : B32 _ _ (19 / 25000000) (63 / 10) :=
    B32.mul bpi b2 (by norm_num [capF]) (by norm_num) (by norm_num)
  have m2 : B32 _ _ (29 / 10000000) (63 / 4) :=
    B32.mul m1 bc (by norm_num [capF]) (by norm_num) (by norm_num)
  have rc : B32 _ _ (1 / 62500000) (637 / 10000) := B32.div (mlo := 15707 / 1000) b1 m2
    (by rw [abs_of_pos (by norm_num [piD])]; norm_num [piD]) (by norm_num) (by norm_num)
    (by norm_num [capF]) (by norm_num)
  have sm : B32 _ _ (1 / 50000000) (331 / 5000) :=
    B32.add bd rc (by norm_num) (by norm_num [capF]) (by norm_num)
  have q : B32 _ _ (7 / 500000000) (189 / 5000) := B32.div (mlo := 661619 / 10000000) bd sm
    (by rw [abs_of_pos (by norm_num [piD])]; norm_num [piD]) (by norm_num) (by norm_num)
    (by norm_num [capF]) (by norm_num)
  refine (a32_shift q.1 (δ := 1 / 10 ^ 8 * 3 / 10) ?_).mono (by norm_num)
  rw [abs_le]; constructor <;> norm_num [piD]

/-- `(float) 1.0` is `1` (`LibmSpec.f64ToF32_exact`). -/
theorem one32 (hL : LibmSpec) :
    (Float.toFloat32 (1.0 : Float)).IsFinite ∧ (Float.toFloat32 (1.0 : Float)).toReal = 1 := by
  obtain ⟨f, e⟩ := hL.f64ToF32_exact 1.0 1.0 f64_isFinite_1p0 f32_isFinite_1p0
    (by rw [f32_toReal_1p0, f64_toReal_1p0])
  exact ⟨f, by rw [e, f64_toReal_1p0]⟩

/-- `calc_lowpass_alpha_dt dt 0` (no filter, `FLTE = 0` on roll and pitch) is `(float) 1.0`, of
value `1`, for every finite `dt ≥ 0`. -/
theorem alpha0 (hL : LibmSpec) {dt c : Float32} (hdt : dt.IsFinite) (hdt0 : 0 ≤ dt.toReal)
    (hc : c.IsFinite) (hcv : c.toReal = 0) :
    calc_lowpass_alpha_dt dt c = Float.toFloat32 (1.0 : Float) ∧
      (calc_lowpass_alpha_dt dt c).IsFinite ∧ (calc_lowpass_alpha_dt dt c).toReal = 1 := by
  have hnd : is_negative_float dt = false :=
    Contracts.Track.Att.isNeg_false hL hdt (by have : (0 : ℝ) < 2 ^ (-24 : ℤ) := by positivity
                                               linarith)
  have hnc : is_negative_float c = false :=
    Contracts.Track.Att.isNeg_false hL hc (by rw [hcv]; norm_num)
  have hzc : is_zero_float c = true := (isZero_iff hc).2 (by rw [hcv]; norm_num)
  have e : calc_lowpass_alpha_dt dt c = Float.toFloat32 (1.0 : Float) := by
    simp only [calc_lowpass_alpha_dt, Id.run, hnd, hnc, hzc, Bool.or_false,
      Bool.false_eq_true, ite_false, ite_true, id_pure_eq]
  exact ⟨e, e ▸ (one32 hL).1, e ▸ (one32 hL).2⟩

/-! ## The slew limiter with `slew_rate_max = 0` -/

/-- `SlewLimiter::modifier` with `slew_rate_max = 0` returns the factor `(float) 1.0`, whatever
its state, inputs, sample and `dt` (both exits: `dt` not positive, `slew_rate_max ≤ 0`). -/
theorem modifier_snd {q : Float32} (hq : q.IsFinite) (h0 : q.toReal = 0) (s : SlewLimiter.State)
    (τ : Float32) (inp : SlewLimiter.Inputs) (x dt : Float32) :
    (SlewLimiter.modifier s { slew_rate_max := q, slew_rate_tau := τ } inp x dt).2 =
      Float.toFloat32 1.0 := by
  have hle : (q ≤ Int32.toFloat32 (0 : Int32)) := by
    rw [Float32.le_iff_toReal_le hq Float32.isFinite_int32_zero, h0, Float32.toReal_int32_zero]
  unfold SlewLimiter.modifier
  simp -zeta only [ite_eq_left hle]
  split
  · rfl
  · extract_lets s0 s1 sr s2 nm da aa jp1 jp2
    have e1 : ∀ s, (jp1 () s).2 = Float.toFloat32 1.0 := fun s => rfl
    have e2 : ∀ s, (jp2 () s).2 = Float.toFloat32 1.0 := by
      intro s; simp only [jp2]; split
      · exact e1 _
      · split <;> exact e1 _
    split
    · exact e2 _
    · split
      · exact e2 _
      · exact e2 _

/-! ## `update_i` writes only the integrator -/

section UpdateI

variable (p : AC_PID.Params) (s : AC_PID.State) (dt i : Float32) (l : Bool)

theorem ui_target : (AC_PID.update_i p s dt l i)._target = s._target := by
  unfold AC_PID.update_i; simp only [Id.run]; split <;> (try split) <;> rfl
theorem ui_error : (AC_PID.update_i p s dt l i)._error = s._error := by
  unfold AC_PID.update_i; simp only [Id.run]; split <;> (try split) <;> rfl
theorem ui_derivative : (AC_PID.update_i p s dt l i)._derivative = s._derivative := by
  unfold AC_PID.update_i; simp only [Id.run]; split <;> (try split) <;> rfl
theorem ui_target_derivative :
    (AC_PID.update_i p s dt l i)._target_derivative = s._target_derivative := by
  unfold AC_PID.update_i; simp only [Id.run]; split <;> (try split) <;> rfl
theorem ui_pid_info : (AC_PID.update_i p s dt l i)._pid_info = s._pid_info := by
  unfold AC_PID.update_i; simp only [Id.run]; split <;> (try split) <;> rfl
theorem ui_flags : (AC_PID.update_i p s dt l i)._flags = s._flags := by
  unfold AC_PID.update_i; simp only [Id.run]; split <;> (try split) <;> rfl
theorem ui_slew_limiter : (AC_PID.update_i p s dt l i)._slew_limiter = s._slew_limiter := by
  unfold AC_PID.update_i; simp only [Id.run]; split <;> (try split) <;> rfl
theorem ui_slew_limit_scale :
    (AC_PID.update_i p s dt l i)._slew_limit_scale = s._slew_limit_scale := by
  unfold AC_PID.update_i; simp only [Id.run]; split <;> (try split) <;> rfl

/-- With `ki ≠ 0`, `dt > 0` and no limit, `update_i` adds `E ki i_scale dt` and clamps to `IMAX`. -/
theorem ui_integrator (hki : is_zero_AP_Float p._ki = false) (hdt : is_positive_float dt = true) :
    (AC_PID.update_i p s dt false i)._integrator =
      constrain_value_line_float (s._integrator + s._error * p._ki * i * dt) (-p._kimax) p._kimax
        (Int32.toUInt32 346) := by
  unfold AC_PID.update_i; simp [Id.run, hki, hdt]

end UpdateI

/-! ## `update_all` as `float` expressions -/

/-- **`AC_PID::update_all`, filter branch** (`_reset_filter = false`), with `limit = false`,
`ki ≠ 0`, `dt > 0`, `slew_rate_max = 0` and `kpdmax ≤ 0` (not positive): the new target, error,
derivative and integrator, and the output `P + D + I`, as `float` expressions (the slew factor is
`(float) 1.0`). -/
theorem update_all_eq (p : AC_PID.Params) (s : AC_PID.State) (inp : AC_PID.Inputs)
    (target meas dt pd isc : Float32)
    (ht : target.IsFinite) (hm : meas.IsFinite) (hr : s._flags._reset_filter = false)
    (hdt : is_positive_float dt = true) (hkpd : is_positive_AP_Float p._kpdmax = false)
    (hki : is_zero_AP_Float p._ki = false) (hsf : p._slew_rate_max.IsFinite)
    (hs0 : p._slew_rate_max.toReal = 0) :
    let T1 := s._target + AC_PID.get_filt_T_alpha p dt * (target - s._target)
    let E1 := s._error + AC_PID.get_filt_E_alpha p dt * ((T1 - meas) - s._error)
    let D1 := s._derivative + AC_PID.get_filt_D_alpha p dt * ((E1 - s._error) / dt - s._derivative)
    let I1 := constrain_value_line_float (s._integrator + E1 * p._ki * isc * dt) (-p._kimax)
      p._kimax (Int32.toUInt32 346)
    let r := AC_PID.update_all p s inp target meas dt false pd isc
    r.1._target = T1 ∧ r.1._error = E1 ∧ r.1._derivative = D1 ∧ r.1._integrator = I1 ∧
      r.1._flags._reset_filter = false ∧ r.1._pid_info.FF = T1 * p._kff ∧
      r.1._pid_info.DFF = (T1 - s._target) / dt * p._kdff ∧
      r.2 = E1 * p._kp * Float.toFloat32 1.0 * pd + D1 * p._kd * Float.toFloat32 1.0 * pd + I1 := by
  intro T1 E1 D1 I1 r
  have ht' : target.isFinite = true := ht
  have hm' : meas.isFinite = true := hm
  simp only [r, AC_PID.update_all, ht', hm', hr, hdt, hkpd, Bool.not_true, Bool.false_or,
    Bool.false_eq_true, ite_false, ite_true, modifier_snd hsf hs0, Id.run, id_pure_eq, ui_target,
    ui_error, ui_derivative, ui_target_derivative, ui_pid_info, ui_flags, ui_slew_limiter,
    ui_slew_limit_scale, ui_integrator p _ dt isc hki hdt]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> trivial

/-- **`AC_PID::update_all`, first tick** (`_reset_filter = true`): the target is the input, the
error `target - meas`, the derivative `0`; the flag is cleared. -/
theorem update_all_reset_eq (p : AC_PID.Params) (s : AC_PID.State) (inp : AC_PID.Inputs)
    (target meas dt pd isc : Float32)
    (ht : target.IsFinite) (hm : meas.IsFinite) (hr : s._flags._reset_filter = true)
    (hdt : is_positive_float dt = true) (hkpd : is_positive_AP_Float p._kpdmax = false)
    (hki : is_zero_AP_Float p._ki = false) (hsf : p._slew_rate_max.IsFinite)
    (hs0 : p._slew_rate_max.toReal = 0) :
    let E0 := target - meas
    let I0 := constrain_value_line_float (s._integrator + E0 * p._ki * isc * dt) (-p._kimax)
      p._kimax (Int32.toUInt32 346)
    let r := AC_PID.update_all p s inp target meas dt false pd isc
    r.1._target = target ∧ r.1._error = E0 ∧ r.1._derivative = (0.0 : Float32) ∧
      r.1._integrator = I0 ∧ r.1._flags._reset_filter = false ∧
      r.2 = E0 * p._kp * Float.toFloat32 1.0 * pd + (0.0 : Float32) * p._kd * Float.toFloat32 1.0 * pd
        + I0 := by
  intro E0 I0 r
  have ht' : target.isFinite = true := ht
  have hm' : meas.isFinite = true := hm
  simp only [r, AC_PID.update_all, ht', hm', hr, hdt, hkpd, Bool.not_true, Bool.false_or,
    Bool.false_eq_true, ite_false, ite_true, modifier_snd hsf hs0, Id.run, id_pure_eq, ui_target,
    ui_error, ui_derivative, ui_target_derivative, ui_pid_info, ui_flags, ui_slew_limiter,
    ui_slew_limit_scale, ui_integrator p _ dt isc hki hdt]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> trivial

/-! ## The ideal law and the error budget -/

/-- The ideal target filter: `T' = T + aT (target - T)`. -/
def pidT (aT T tg : ℝ) : ℝ := T + aT * (tg - T)
/-- The ideal error filter: `E' = E + aE ((T' - meas) - E)`. -/
def pidE (aE E T' m : ℝ) : ℝ := E + aE * ((T' - m) - E)
/-- The ideal derivative filter: `D' = D + aD ((E' - E) / dt - D)`. -/
def pidD (aD D E' E dt : ℝ) : ℝ := D + aD * ((E' - E) / dt - D)
/-- The ideal integrator: `I' = clamp(I + ki dt E', -IMAX, IMAX)`. -/
def pidI (ki dt imax I E' : ℝ) : ℝ := max (-imax) (min imax (I + ki * dt * E'))
/-- The ideal output: `kp E' + kd D' + I'`. -/
def pidOut (kp kd E' D' I' : ℝ) : ℝ := kp * E' + kd * D' + I'

/-- The region `|T| ≤ 8`, `|E| ≤ 16`, `|D| ≤ 16384`, `|I| ≤ IMAX` is mapped into itself by the
ideal law (for `|target|, |meas| ≤ 8`, coefficients in `[0, 1]`, `dt = 1/400`). -/
theorem ideal_region {aT aE aD ki imax T E D I tg m : ℝ} (haT0 : 0 ≤ aT) (haT1 : aT ≤ 1)
    (haE0 : 0 ≤ aE) (haE1 : aE ≤ 1) (haD0 : 0 ≤ aD) (haD1 : aD ≤ 1) (himax : 0 ≤ imax)
    (htg : |tg| ≤ 8) (hm : |m| ≤ 8) (hT : |T| ≤ 8) (hE : |E| ≤ 16) (hD : |D| ≤ 16384) :
    |pidT aT T tg| ≤ 8 ∧ |pidE aE E (pidT aT T tg) m| ≤ 16 ∧
      |pidD aD D (pidE aE E (pidT aT T tg) m) E dtR| ≤ 16384 ∧
      |pidI ki dtR imax I (pidE aE E (pidT aT T tg) m)| ≤ imax := by
  have h1 : |pidT aT T tg| ≤ 8 := convex_abs_le hT htg haT0 haT1
  have h2 : |pidE aE E (pidT aT T tg) m| ≤ 16 :=
    convex_abs_le hE ((abs_sub _ _).trans (by linarith)) haE0 haE1
  refine ⟨h1, h2, convex_abs_le hD ?_ haD0 haD1, ?_⟩
  · rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < dtR), div_le_iff₀ (by norm_num)]
    have := abs_sub (pidE aE E (pidT aT T tg) m) E
    norm_num at this ⊢; linarith
  · unfold pidI; rw [abs_le]
    constructor
    · exact le_max_left _ _
    · exact max_le (by linarith) (min_le_left _ _)

/-- **The error budget of one PID step** (filter branch), for any gains in the mission's ranges
(`0 ≤ kp ≤ 0.31`, `0 ≤ ki ≤ 0.14`, `0 ≤ kd ≤ 0.004`, `IMAX = 1/2`), the 20 Hz target and
derivative filters, an error-filter coefficient `aE ∈ [0, 1]` known within `2⁻²³`, scale factors
of value `1`, `dt = 1/400`, on the region `|target|, |meas|, |T| ≤ 8`, `|E| ≤ 16`, `|D| ≤ 16384`,
`|I| ≤ 1/2`. -/
theorem pid_num {Tg M T E D I aT aE aD kp ki kd dt pd isc one kimax : Float32}
    {aEr kpr kir kdr : ℝ}
    (fTg : Tg.IsFinite) (fM : M.IsFinite) (fT : T.IsFinite) (fE : E.IsFinite) (fD : D.IsFinite)
    (fI : I.IsFinite) (rTg : |Tg.toReal| ≤ 8) (rM : |M.toReal| ≤ 8) (rT : |T.toReal| ≤ 8)
    (rE : |E.toReal| ≤ 16) (rD : |D.toReal| ≤ 16384) (rI : |I.toReal| ≤ 1 / 2)
    (hdt : dt.IsFinite) (hdtv : dt.toReal = dtR)
    (haT : A32 aT α20 (1 / 2 ^ 23)) (haD : A32 aD α20 (1 / 2 ^ 23))
    (haE : A32 aE aEr (1 / 2 ^ 23)) (haE0 : 0 ≤ aEr) (haE1 : aEr ≤ 1)
    (hkp : kp.IsFinite) (hkpv : kp.toReal = kpr) (hkp0 : 0 ≤ kpr) (hkp1 : kpr ≤ 31 / 100)
    (hki : ki.IsFinite) (hkiv : ki.toReal = kir) (hki0 : 0 ≤ kir) (hki1 : kir ≤ 14 / 100)
    (hkd : kd.IsFinite) (hkdv : kd.toReal = kdr) (hkd0 : 0 ≤ kdr) (hkd1 : kdr ≤ 4 / 1000)
    (hpd : pd.IsFinite) (hpdv : pd.toReal = 1) (hisc : isc.IsFinite) (hiscv : isc.toReal = 1)
    (hone : one.IsFinite) (honev : one.toReal = 1)
    (hkimax : kimax.IsFinite) (hkimaxv : kimax.toReal = 1 / 2) :
    let T1 := T + aT * (Tg - T)
    let E1 := E + aE * ((T1 - M) - E)
    let D1 := D + aD * ((E1 - E) / dt - D)
    let I1 := constrain_value_line_float (I + E1 * ki * isc * dt) (-kimax) kimax (Int32.toUInt32 346)
    let out := E1 * kp * one * pd + D1 * kd * one * pd + I1
    let Tr := pidT α20 T.toReal Tg.toReal
    let Er := pidE aEr E.toReal Tr M.toReal
    let Dr := pidD α20 D.toReal Er E.toReal dtR
    let Ir := pidI kir dtR (1 / 2) I.toReal Er
    A32 T1 Tr (1 / 312500) ∧ A32 E1 Er (3 / 200000) ∧ A32 D1 Dr (39 / 5000) ∧
      A32 I1 Ir (37 / 1000000000) ∧ A32 out (pidOut kpr kdr Er Dr Ir) (51 / 1000000) := by
  intro T1 E1 D1 I1 out Tr Er Dr Ir
  have bTg : B32 Tg Tg.toReal 0 8 := B32.of_exact fTg rTg
  have bM : B32 M M.toReal 0 8 := B32.of_exact fM rM
  have bT : B32 T T.toReal 0 8 := B32.of_exact fT rT
  have bE : B32 E E.toReal 0 16 := B32.of_exact fE rE
  have bD : B32 D D.toReal 0 16384 := B32.of_exact fD rD
  have bI : B32 I I.toReal 0 (1 / 2) := B32.of_exact fI rI
  have bdt : B32 dt dtR 0 dtR := B32.lit hdt hdtv (by norm_num)
  have baT : B32 aT α20 (1 / 2 ^ 23) (1 / 4) := ⟨haT, by norm_num⟩
  have baD : B32 aD α20 (1 / 2 ^ 23) (1 / 4) := ⟨haD, by norm_num⟩
  have baE : B32 aE aEr (1 / 2 ^ 23) 1 := ⟨haE, by rw [abs_of_nonneg haE0]; exact haE1⟩
  have bkp : B32 kp kpr 0 (31 / 100) := B32.lit hkp hkpv (by rw [abs_of_nonneg hkp0]; exact hkp1)
  have bki : B32 ki kir 0 (14 / 100) := B32.lit hki hkiv (by rw [abs_of_nonneg hki0]; exact hki1)
  have bkd : B32 kd kdr 0 (4 / 1000) := B32.lit hkd hkdv (by rw [abs_of_nonneg hkd0]; exact hkd1)
  -- the target filter
  have s1 : B32 (Tg - T) _ (3 / 3125000) 16 :=
    B32.sub bTg bT (by norm_num) (by norm_num [capF]) (by norm_num)
  have s2 : B32 (aT * (Tg - T)) _ (3 / 1250000) 4 :=
    B32.mul baT s1 (by norm_num [capF]) (by norm_num) (by norm_num)
  have t1' : B32 T1 _ (1 / 312500) 12 :=
    B32.add bT s2 (by norm_num) (by norm_num [capF]) (by norm_num)
  have t1 : B32 T1 Tr (1 / 312500) 8 :=
    ⟨t1'.1, convex_abs_le rT rTg (by norm_num) (by norm_num)⟩
  -- the error filter
  have s3 : B32 (T1 - M) _ (21 / 5000000) 16 :=
    B32.sub t1 bM (by norm_num) (by norm_num [capF]) (by norm_num)
  have s4 : B32 (T1 - M - E) _ (31 / 5000000) 32 :=
    B32.sub s3 bE (by norm_num) (by norm_num [capF]) (by norm_num)
  have s5 : B32 (aE * (T1 - M - E)) _ (3 / 250000) 32 :=
    B32.mul baE s4 (by norm_num [capF]) (by norm_num) (by norm_num)
  have e1' : B32 E1 _ (3 / 200000) 48 :=
    B32.add bE s5 (by norm_num) (by norm_num [capF]) (by norm_num)
  have e1 : B32 E1 Er (3 / 200000) 16 :=
    ⟨e1'.1, convex_abs_le rE ((abs_sub _ _).trans (by linarith [t1.2])) haE0 haE1⟩
  -- the derivative filter
  have s6 : B32 (E1 - E) _ (17 / 1000000) 32 :=
    B32.sub e1 bE (by norm_num) (by norm_num [capF]) (by norm_num)
  have s7 : B32 ((E1 - E) / dt) _ (19 / 2500) 12801 := B32.div (mlo := dtR) s6 bdt
    (by norm_num) (by norm_num) (by norm_num) (by norm_num [capF]) (by norm_num)
  have s8 : B32 ((E1 - E) / dt - D) _ (47 / 5000) 29185 :=
    B32.sub s7 bD (by norm_num) (by norm_num [capF]) (by norm_num)
  have s9 : B32 (aD * ((E1 - E) / dt - D)) _ (63 / 10000) (29185 / 4) :=
    B32.mul baD s8 (by norm_num [capF]) (by norm_num) (by norm_num)
  have d1' : B32 D1 _ (39 / 5000) (94721 / 4) :=
    B32.add bD s9 (by norm_num) (by norm_num [capF]) (by norm_num)
  have d1 : B32 D1 Dr (39 / 5000) 16384 := by
    refine ⟨d1'.1, convex_abs_le rD ?_ (by norm_num) (by norm_num)⟩
    rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < dtR), div_le_iff₀ (by norm_num)]
    have := abs_sub Er E.toReal
    have := e1.2
    norm_num at this ⊢; linarith
  -- the integrator
  have s10 : B32 (E1 * ki) _ (23 / 10000000) (56 / 25) :=
    B32.mul e1 bki (by norm_num [capF]) (by norm_num) (by norm_num)
  have s11 := b32_mul_one s10 hisc hiscv
  have s12 : B32 (E1 * ki * isc * dt) _ (61 / 10000000000) (3 / 500) :=
    B32.mul s11 bdt (by norm_num [capF]) (by norm_num) (by norm_num)
  have s13 : B32 (I + E1 * ki * isc * dt) _ (37 / 1000000000) (253 / 500) :=
    B32.add bI s12 (by norm_num) (by norm_num [capF]) (by norm_num)
  have fnk : (-kimax).IsFinite := (Float32.isFinite_neg _).2 hkimax
  obtain ⟨fI1, eI1⟩ := constrain_spec (Int32.toUInt32 346) s13.1.1 fnk hkimax
    (by rw [Float32.toReal_neg, hkimaxv]; norm_num)
  rw [Float32.toReal_neg, hkimaxv] at eI1
  have i1 : B32 I1 Ir (37 / 1000000000) (1 / 2) := by
    refine ⟨⟨fI1, ?_⟩, ?_⟩
    · show |I1.toReal - max (-(1 / 2)) (min (1 / 2) (I.toReal + kir * dtR * Er))| ≤ _
      rw [eI1, show kir * dtR * Er = Er * kir * dtR by ring]
      exact (clamp_lip _ _ _).trans s13.1.2
    · show |max (-(1 / 2)) (min (1 / 2) (I.toReal + kir * dtR * Er))| ≤ 1 / 2
      rw [abs_le]
      exact ⟨le_max_left _ _, max_le (by norm_num) (min_le_left _ _)⟩
  -- the output
  have p1 : B32 (E1 * kp) _ (1 / 200000) (124 / 25) :=
    B32.mul e1 bkp (by norm_num [capF]) (by norm_num) (by norm_num)
  have p2 := b32_mul_one (b32_mul_one p1 hone honev) hpd hpdv
  have q1 : B32 (D1 * kd) _ (9 / 250000) (8192 / 125) :=
    B32.mul d1 bkd (by norm_num [capF]) (by norm_num) (by norm_num)
  have q2 := b32_mul_one (b32_mul_one q1 hone honev) hpd hpdv
  have pq : B32 (E1 * kp * one * pd + D1 * kd * one * pd) _ (23 / 500000) (8812 / 125) :=
    B32.add p2 q2 (by norm_num) (by norm_num [capF]) (by norm_num)
  have o : B32 out _ (51 / 1000000) 71 :=
    B32.add pq i1 (by norm_num) (by norm_num [capF]) (by norm_num)
  exact ⟨t1.1, e1.1, d1.1, i1.1, o.1.congr (by simp only [pidOut]; ring)⟩

/-! ## The rate PIDs with the mission's parameters -/

/-- The parameters of one rate PID as values: gains `kp ki kd`, error-filter cutoff `fE`, and the
mission's common settings (`FF = DFF = 0`, `IMAX = 0.5`, `FLTT = FLTD = 20 Hz`, `SMAX = 0`,
`PDMX = 0`). -/
structure RateGains (q : AC_PID.Params) (kp ki kd fE : ℝ) : Prop where
  kp_fin : q._kp.IsFinite
  kp_val : q._kp.toReal = kp
  ki_fin : q._ki.IsFinite
  ki_val : q._ki.toReal = ki
  kd_fin : q._kd.IsFinite
  kd_val : q._kd.toReal = kd
  kff_fin : q._kff.IsFinite
  kff_val : q._kff.toReal = 0
  kdff_fin : q._kdff.IsFinite
  kdff_val : q._kdff.toReal = 0
  kimax_fin : q._kimax.IsFinite
  kimax_val : q._kimax.toReal = 1 / 2
  fT_fin : q._filt_T_hz.IsFinite
  fT_val : q._filt_T_hz.toReal = 20
  fE_fin : q._filt_E_hz.IsFinite
  fE_val : q._filt_E_hz.toReal = fE
  fD_fin : q._filt_D_hz.IsFinite
  fD_val : q._filt_D_hz.toReal = 20
  slew_fin : q._slew_rate_max.IsFinite
  slew_val : q._slew_rate_max.toReal = 0
  kpdmax_fin : q._kpdmax.IsFinite
  kpdmax_val : q._kpdmax.toReal = 0

theorem isPosAP_false {x : Float32} (hx : x.IsFinite) (h : x.toReal < 2 ^ (-23 : ℤ)) :
    is_positive_AP_Float x = false := by
  rcases hz : is_positive_AP_Float x with _ | _
  · rfl
  · have := (isPosAP_iff hx).1 hz; linarith

theorem dt_pos {dt : Float32} (hdt : dt.IsFinite) (hdtv : dt.toReal = dtR) :
    is_positive_float dt = true := isPos_true hdt (by rw [hdtv]; norm_num)

/-- **C11, one rate PID step** (`AC_PID::update_all`, filter branch, `limit = false`): for gains
`0 < ki ≤ 0.14` (at least `1/100`), `0 ≤ kp ≤ 0.31`, `0 ≤ kd ≤ 0.004`, an error-filter coefficient
known within `2⁻²³` of `aE ∈ [0, 1]`, scale factors of value `1`, `dt = 1/400`, on the region
`|target|, |meas|, |T| ≤ 8`, `|E| ≤ 16`, `|D| ≤ 16384`, `|I| ≤ 1/2`: the new target, error,
derivative, integrator and the output are within `3.2·10⁻⁶`, `1.5·10⁻⁵`, `7.8·10⁻³`,
`3.7·10⁻⁸`, `5.1·10⁻⁵` of the ideal law; the feed-forward terms are `0`. -/
theorem update_all_spec (hL : LibmSpec) {q : AC_PID.Params} {kp ki kd fE aE : ℝ}
    (g : RateGains q kp ki kd fE) (s : AC_PID.State) (inp : AC_PID.Inputs)
    (target meas dt pd isc : Float32)
    (hkp0 : 0 ≤ kp) (hkp1 : kp ≤ 31 / 100) (hki0 : 1 / 100 ≤ ki) (hki1 : ki ≤ 14 / 100)
    (hkd0 : 0 ≤ kd) (hkd1 : kd ≤ 4 / 1000)
    (haE : A32 (calc_lowpass_alpha_dt dt q._filt_E_hz) aE (1 / 2 ^ 23)) (haE0 : 0 ≤ aE)
    (haE1 : aE ≤ 1) (hdt : dt.IsFinite) (hdtv : dt.toReal = dtR)
    (hpd : pd.IsFinite) (hpdv : pd.toReal = 1) (hisc : isc.IsFinite) (hiscv : isc.toReal = 1)
    (hr : s._flags._reset_filter = false)
    (ft : target.IsFinite) (fm : meas.IsFinite) (fT : s._target.IsFinite)
    (fE : s._error.IsFinite) (fD : s._derivative.IsFinite) (fI : s._integrator.IsFinite)
    (rt : |target.toReal| ≤ 8) (rm : |meas.toReal| ≤ 8) (rT : |s._target.toReal| ≤ 8)
    (rE : |s._error.toReal| ≤ 16) (rD : |s._derivative.toReal| ≤ 16384)
    (rI : |s._integrator.toReal| ≤ 1 / 2) :
    let r := AC_PID.update_all q s inp target meas dt false pd isc
    let Tr := pidT α20 s._target.toReal target.toReal
    let Er := pidE aE s._error.toReal Tr meas.toReal
    let Dr := pidD α20 s._derivative.toReal Er s._error.toReal dtR
    let Ir := pidI ki dtR (1 / 2) s._integrator.toReal Er
    A32 r.1._target Tr (1 / 312500) ∧ A32 r.1._error Er (3 / 200000) ∧
      A32 r.1._derivative Dr (39 / 5000) ∧ A32 r.1._integrator Ir (37 / 1000000000) ∧
      A32 r.2 (pidOut kp kd Er Dr Ir) (51 / 1000000) ∧
      r.1._flags._reset_filter = false ∧ AC_PID.get_ff r.1 = r.1._pid_info.FF + r.1._pid_info.DFF ∧
      r.1._pid_info.FF.IsFinite ∧ r.1._pid_info.FF.toReal = 0 ∧
      r.1._pid_info.DFF.IsFinite ∧ r.1._pid_info.DFF.toReal = 0 := by
  intro r Tr Er Dr Ir
  have hpos := dt_pos hdt hdtv
  have hkpd : is_positive_AP_Float q._kpdmax = false :=
    isPosAP_false g.kpdmax_fin (by rw [g.kpdmax_val]; positivity)
  have hzki : is_zero_AP_Float q._ki = false := by
    rw [isZeroAP_eq]; exact isZero_false g.ki_fin (by
      rw [g.ki_val, abs_of_pos (by linarith)]; norm_num; linarith)
  obtain ⟨eT, eE, eD, eI, eR, eFF, eDFF, eO⟩ :=
    update_all_eq q s inp target meas dt pd isc ft fm hr hpos hkpd hzki g.slew_fin g.slew_val
  have haT := alpha20 hL hdt hdtv g.fT_fin g.fT_val
  have haD := alpha20 hL hdt hdtv g.fD_fin g.fD_val
  obtain ⟨n1, n2, n3, n4, n5⟩ := pid_num (one := Float.toFloat32 1.0) (kimax := q._kimax)
    (kp := q._kp) (ki := q._ki) (kd := q._kd) (isc := isc) (pd := pd)
    ft fm fT fE fD fI rt rm rT rE rD rI hdt hdtv haT haD haE haE0 haE1
    g.kp_fin g.kp_val hkp0 hkp1 g.ki_fin g.ki_val (by linarith) hki1 g.kd_fin g.kd_val hkd0 hkd1
    hpd hpdv hisc hiscv (one32 hL).1 (one32 hL).2 g.kimax_fin g.kimax_val
  have hT1 := n1.1
  -- the feed-forward terms: products with `kff = kdff = 0`
  have fdiv : ((s._target + AC_PID.get_filt_T_alpha q dt * (target - s._target) - s._target) /
      dt).IsFinite := by
    have b1 : B32 (s._target + AC_PID.get_filt_T_alpha q dt * (target - s._target)) Tr
        (1 / 312500) 8 := ⟨n1, convex_abs_le rT rt (by norm_num) (by norm_num)⟩
    have b2 := B32.sub (R := 16) (e := 1 / 100000) b1 (B32.of_exact fT rT) (by norm_num)
      (by norm_num [capF]) (by norm_num)
    have bd : B32 dt dtR 0 dtR := B32.lit hdt hdtv (by norm_num)
    exact (B32.div (mlo := dtR) b2 bd (by norm_num) (by norm_num) (by norm_num) (R := 6401)
      (by norm_num [capF]) (by norm_num) (e := 1 / 100)).1.1
  have ff1 := Float32.mul_zero_val hT1 g.kff_fin g.kff_val
  have ff2 := Float32.mul_zero_val fdiv g.kdff_fin g.kdff_val
  refine ⟨eT ▸ n1, eE ▸ n2, eD ▸ n3, eI ▸ n4, eO ▸ n5, eR, rfl, ?_, ?_, ?_, ?_⟩
  · rw [eFF]; exact ff1.1
  · rw [eFF]; exact ff1.2
  · rw [eDFF]; exact ff2.1
  · rw [eDFF]; exact ff2.2

/-- The conclusion of `update_all_spec` for one PID: new state `s'` and output `out` against the
ideal law from the old values `T E D I`, the target `tg` and the measurement `m`. -/
def PIDStepSpec (aE kp ki kd T E D I tg m : ℝ) (s' : AC_PID.State) (out : Float32) : Prop :=
  A32 s'._target (pidT α20 T tg) (1 / 312500) ∧
  A32 s'._error (pidE aE E (pidT α20 T tg) m) (3 / 200000) ∧
  A32 s'._derivative (pidD α20 D (pidE aE E (pidT α20 T tg) m) E dtR) (39 / 5000) ∧
  A32 s'._integrator (pidI ki dtR (1 / 2) I (pidE aE E (pidT α20 T tg) m)) (37 / 1000000000) ∧
  A32 out (pidOut kp kd (pidE aE E (pidT α20 T tg) m)
    (pidD α20 D (pidE aE E (pidT α20 T tg) m) E dtR)
    (pidI ki dtR (1 / 2) I (pidE aE E (pidT α20 T tg) m))) (51 / 1000000)

/-- The feed-forward output `get_ff` of a PID state is a finite `0`. -/
def FFZero (q : AC_PID.State) : Prop := (AC_PID.get_ff q).IsFinite ∧ (AC_PID.get_ff q).toReal = 0

/-- The roll and pitch rate gains: `P = I = 0.135`, `D = 0.0036`, `FLTE = 0`. -/
abbrev kpRP : ℝ := 9059697 / 67108864
abbrev kdRP : ℝ := 7730941 / 2147483648
/-- The yaw rate gains: `P = 0.3`, `I = 0.02`, `D = 0`, `FLTE = 2.5`. -/
abbrev kpY : ℝ := 5033165 / 16777216
abbrev kiY : ℝ := 5368709 / 268435456

/-- **C11, roll/pitch PID** with the mission's gains: `aE = 1` (no error filter). -/
theorem roll_pid_spec (hL : LibmSpec) {q : AC_PID.Params} (g : RateGains q kpRP kpRP kdRP 0)
    (s : AC_PID.State) (inp : AC_PID.Inputs) (target meas dt pd isc : Float32)
    (hdt : dt.IsFinite) (hdtv : dt.toReal = dtR)
    (hpd : pd.IsFinite) (hpdv : pd.toReal = 1) (hisc : isc.IsFinite) (hiscv : isc.toReal = 1)
    (hr : s._flags._reset_filter = false)
    (ft : target.IsFinite) (fm : meas.IsFinite) (fT : s._target.IsFinite)
    (fE : s._error.IsFinite) (fD : s._derivative.IsFinite) (fI : s._integrator.IsFinite)
    (rt : |target.toReal| ≤ 8) (rm : |meas.toReal| ≤ 8) (rT : |s._target.toReal| ≤ 8)
    (rE : |s._error.toReal| ≤ 16) (rD : |s._derivative.toReal| ≤ 16384)
    (rI : |s._integrator.toReal| ≤ 1 / 2) :
    PIDStepSpec 1 kpRP kpRP kdRP s._target.toReal s._error.toReal s._derivative.toReal
      s._integrator.toReal target.toReal meas.toReal
      (AC_PID.update_all q s inp target meas dt false pd isc).1
      (AC_PID.update_all q s inp target meas dt false pd isc).2 ∧
    FFZero (AC_PID.update_all q s inp target meas dt false pd isc).1 := by
  obtain ⟨-, f1, e1⟩ := alpha0 hL hdt (by rw [hdtv]; norm_num) g.fE_fin g.fE_val
  have haE : A32 (calc_lowpass_alpha_dt dt q._filt_E_hz) 1 (1 / 2 ^ 23) :=
    (A32.of_exact f1).congr e1 |>.mono (by norm_num)
  obtain ⟨h1, h2, h3, h4, h5, -, hff, f1, v1, f2, v2⟩ := update_all_spec hL g s inp target meas dt
    pd isc (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    haE (by norm_num) (by norm_num) hdt hdtv hpd hpdv hisc hiscv hr ft fm fT fE fD fI
    rt rm rT rE rD rI
  have := Float32.add_zero_val f1 f2 v2
  exact ⟨⟨h1, h2, h3, h4, h5⟩, hff ▸ this.1, hff ▸ this.2.trans v1⟩

/-- **C11, yaw PID** with the mission's gains: `aE = α2p5` (the 2.5 Hz error filter). -/
theorem yaw_pid_spec (hL : LibmSpec) {q : AC_PID.Params} (g : RateGains q kpY kiY 0 (5 / 2))
    (s : AC_PID.State) (inp : AC_PID.Inputs) (target meas dt pd isc : Float32)
    (hdt : dt.IsFinite) (hdtv : dt.toReal = dtR)
    (hpd : pd.IsFinite) (hpdv : pd.toReal = 1) (hisc : isc.IsFinite) (hiscv : isc.toReal = 1)
    (hr : s._flags._reset_filter = false)
    (ft : target.IsFinite) (fm : meas.IsFinite) (fT : s._target.IsFinite)
    (fE : s._error.IsFinite) (fD : s._derivative.IsFinite) (fI : s._integrator.IsFinite)
    (rt : |target.toReal| ≤ 8) (rm : |meas.toReal| ≤ 8) (rT : |s._target.toReal| ≤ 8)
    (rE : |s._error.toReal| ≤ 16) (rD : |s._derivative.toReal| ≤ 16384)
    (rI : |s._integrator.toReal| ≤ 1 / 2) :
    PIDStepSpec α2p5 kpY kiY 0 s._target.toReal s._error.toReal s._derivative.toReal
      s._integrator.toReal target.toReal meas.toReal
      (AC_PID.update_all q s inp target meas dt false pd isc).1
      (AC_PID.update_all q s inp target meas dt false pd isc).2 ∧
    FFZero (AC_PID.update_all q s inp target meas dt false pd isc).1 := by
  have haE : A32 (calc_lowpass_alpha_dt dt q._filt_E_hz) α2p5 (1 / 2 ^ 23) :=
    (alpha2p5 hL hdt hdtv g.fE_fin g.fE_val).mono (by norm_num)
  obtain ⟨h1, h2, h3, h4, h5, -, hff, f1, v1, f2, v2⟩ := update_all_spec hL g s inp target meas dt
    pd isc (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    haE (by norm_num) (by norm_num) hdt hdtv hpd hpdv hisc hiscv hr ft fm fT fE fD fI
    rt rm rT rE rD rI
  have := Float32.add_zero_val f1 f2 v2
  exact ⟨⟨h1, h2, h3, h4, h5⟩, hff ▸ this.1, hff ▸ this.2.trans v1⟩

/-- **C11, first tick** (`_reset_filter = true`): `T' = target`, `D' = 0`, and `E' = target - meas`
within `10⁻⁶` (one rounding) for `|target|, |meas| ≤ 8`. -/
theorem reset_pid_spec {q : AC_PID.Params} {kp ki kd fE : ℝ} (g : RateGains q kp ki kd fE)
    (hki0 : 1 / 100 ≤ ki) (s : AC_PID.State) (inp : AC_PID.Inputs) (target meas dt pd isc : Float32)
    (hdt : dt.IsFinite) (hdtv : dt.toReal = dtR) (hr : s._flags._reset_filter = true)
    (ft : target.IsFinite) (fm : meas.IsFinite) (rt : |target.toReal| ≤ 8)
    (rm : |meas.toReal| ≤ 8) :
    let r := AC_PID.update_all q s inp target meas dt false pd isc
    r.1._target = target ∧ r.1._derivative = (0.0 : Float32) ∧
      A32 r.1._error (target.toReal - meas.toReal) (1 / 1000000) ∧
      r.1._flags._reset_filter = false := by
  intro r
  have hpos := dt_pos hdt hdtv
  have hkpd : is_positive_AP_Float q._kpdmax = false :=
    isPosAP_false g.kpdmax_fin (by rw [g.kpdmax_val]; positivity)
  have hzki : is_zero_AP_Float q._ki = false := by
    rw [isZeroAP_eq]; exact isZero_false g.ki_fin (by
      rw [g.ki_val, abs_of_pos (by linarith)]; norm_num; linarith)
  obtain ⟨eT, eE, eD, -, eR, -⟩ :=
    update_all_reset_eq q s inp target meas dt pd isc ft fm hr hpos hkpd hzki g.slew_fin g.slew_val
  refine ⟨eT, eD, ?_, eR⟩
  rw [eE]
  exact (B32.sub (R := 16) (e := 1 / 1000000) (B32.of_exact ft rt) (B32.of_exact fm rm)
    (by norm_num) (by norm_num [capF]) (by norm_num)).1

/-! ## The rate controller -/

section Rate

open AC_AttitudeControl_Multi

/-- `update_throttle_gain_boost` writes only the scale vectors. -/
theorem gain_boost_shape (p : Params) (s : State) (inp : Inputs) :
    ∃ X Y : Vector3f.State,
      update_throttle_gain_boost p s inp = { s with _pd_scale := X, _angle_P_scale := Y } := by
  unfold update_throttle_gain_boost set_PD_scale_mult set_angle_P_scale_mult
  simp only [Id.run, id_pure_eq]
  split
  · exact ⟨_, _, rfl⟩
  · exact ⟨s._pd_scale, s._angle_P_scale, rfl⟩

/-- `update_throttle_rpy_mix` writes only `_throttle_rpy_mix`. -/
theorem rpy_mix_shape (s : State) (inp : Inputs) :
    ∃ m : Float32, update_throttle_rpy_mix s inp = { s with _throttle_rpy_mix := m } := by
  unfold update_throttle_rpy_mix
  simp only [Id.run, id_pure_eq]
  split_ifs <;> exact ⟨_, rfl⟩

/-- `(float) 2.0` is `2`. -/
theorem two32 (hL : LibmSpec) :
    (Float.toFloat32 (2.0 : Float)).IsFinite ∧ (Float.toFloat32 (2.0 : Float)).toReal = 2 := by
  obtain ⟨f, e⟩ := hL.f64ToF32_exact 2.0 2.0 f64_isFinite_2p0 f32_isFinite_2p0
    (by rw [f32_toReal_2p0, f64_toReal_2p0])
  exact ⟨f, by rw [e, f64_toReal_2p0]⟩

/-- A vector of `float`s of value `1`. -/
def Ones (v : Vector3f.State) : Prop :=
  v.x.IsFinite ∧ v.x.toReal = 1 ∧ v.y.IsFinite ∧ v.y.toReal = 1 ∧ v.z.IsFinite ∧ v.z.toReal = 1

/-- With `ATC_THR_G_BOOST = 0`, the gain boost leaves PD scale factors of value `1` at value `1`. -/
theorem gain_boost_pd (hL : LibmSpec) (p : Params) (s : State) (inp : Inputs)
    (hgb : p._throttle_gain_boost.IsFinite) (hgb0 : p._throttle_gain_boost.toReal = 0)
    (h1 : Ones s._pd_scale) : Ones (update_throttle_gain_boost p s inp)._pd_scale := by
  unfold update_throttle_gain_boost set_PD_scale_mult set_angle_P_scale_mult
  simp only [Id.run, id_pure_eq]
  split
  · obtain ⟨fa, ea⟩ := Float32.add_exact hgb f32_isFinite_1p0 f32_isFinite_1p0
      (by rw [hgb0, f32_toReal_1p0]; ring)
    rw [f32_toReal_1p0] at ea
    have hb := constrain_inside (Int32.toUInt32 (420 : Int32)) fa (one32 hL).1 (two32 hL).1
      (by rw [ea, (one32 hL).2]) (by rw [ea, (two32 hL).2]; norm_num)
    rw [hb]
    obtain ⟨x1, x2, y1, y2, z1, z2⟩ := h1
    have mx := mul_one_val x1 fa ea
    have my := mul_one_val y1 fa ea
    have mz := mul_one_val z1 f32_isFinite_1p0 f32_toReal_1p0
    exact ⟨mx.1, mx.2.trans x2, my.1, my.2.trans y2, mz.1, mz.2.trans z2⟩
  · exact h1

/-- The rate controller as three `update_all` calls (`rate_controller_run_dt`), on the state `s2`
after the gain boost and the mix update. -/
theorem rate_run_eq (p : Params) (s : State) (o : Outputs) (inp : Inputs) :
    let s2 := update_throttle_rpy_mix (update_throttle_gain_boost p s inp) inp
    let ab := (Vector3f.op_add_assign s._ang_vel_body_rads s2._sysid_ang_vel_body_rads).1
    let g := inp.get_gyro_latest
    let R := AC_PID.update_all p._pid_rate_roll s2._pid_rate_roll inp._pid_rate_roll ab.x g.x
      s._dt_s inp.limit_roll s2._pd_scale.x s2._i_scale.x
    let P := AC_PID.update_all p._pid_rate_pitch s2._pid_rate_pitch inp._pid_rate_pitch ab.y g.y
      s._dt_s inp.limit_pitch s2._pd_scale.y s2._i_scale.y
    let Y := AC_PID.update_all p._pid_rate_yaw s2._pid_rate_yaw inp._pid_rate_yaw ab.z g.z
      s._dt_s inp.limit_yaw s2._pd_scale.z s2._i_scale.z
    let r := rate_controller_run p s o inp
    r.1._pid_rate_roll = R.1 ∧ r.1._pid_rate_pitch = P.1 ∧ r.1._pid_rate_yaw = Y.1 ∧
      r.2.set_roll = R.2 + s2._actuator_sysid.x ∧ r.2.set_pitch = P.2 + s2._actuator_sysid.y ∧
      r.2.set_yaw = Y.2 + s2._actuator_sysid.z ∧ r.2.set_roll_ff = AC_PID.get_ff R.1 ∧
      r.2.set_pitch_ff = AC_PID.get_ff P.1 ∧
      r.2.set_yaw_ff = AC_PID.get_ff Y.1 * s2._feedforward_scalar := by
  intro s2 ab g R P Y r
  simp only [r, R, P, Y, s2, ab, g, rate_controller_run, rate_controller_run_dt, Id.run, id_pure_eq,
    and_self]

/-- A vector of finite `float`s of value `0`. -/
def Zeros (v : Vector3f.State) : Prop :=
  v.x.IsFinite ∧ v.x.toReal = 0 ∧ v.y.IsFinite ∧ v.y.toReal = 0 ∧ v.z.IsFinite ∧ v.z.toReal = 0

/-- The region of one PID state: finite, `|T| ≤ 8`, `|E| ≤ 16`, `|D| ≤ 16384`, `|I| ≤ 1/2`, and
past its first tick (`_reset_filter = false`). -/
structure PIDRegion (q : AC_PID.State) : Prop where
  fT : q._target.IsFinite
  fE : q._error.IsFinite
  fD : q._derivative.IsFinite
  fI : q._integrator.IsFinite
  rT : |q._target.toReal| ≤ 8
  rE : |q._error.toReal| ≤ 16
  rD : |q._derivative.toReal| ≤ 16384
  rI : |q._integrator.toReal| ≤ 1 / 2
  reset : q._flags._reset_filter = false

/-- A finite `float` vector with components at most `8` in magnitude. -/
def VBox8 (v : Vector3f.State) : Prop :=
  v.x.IsFinite ∧ |v.x.toReal| ≤ 8 ∧ v.y.IsFinite ∧ |v.y.toReal| ≤ 8 ∧ v.z.IsFinite ∧
    |v.z.toReal| ≤ 8

theorem pidStep_congr_out {aE kp ki kd T E D I tg m : ℝ} {s' : AC_PID.State} {out out' : Float32}
    (h : PIDStepSpec aE kp ki kd T E D I tg m s' out) (hf : out'.IsFinite)
    (hv : out'.toReal = out.toReal) : PIDStepSpec aE kp ki kd T E D I tg m s' out' :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, A32.congr_x h.2.2.2.2 hf hv⟩

/-- **C11, the rate controller** (`rate_controller_run`, one tick) with the mission's parameters:
the motors' roll, pitch and yaw inputs are the outputs of the three PID steps (`roll_pid_spec`,
`yaw_pid_spec`) with target the body-rate target `_ang_vel_body_rads` and measurement the gyro
`get_gyro_latest`, the new PID states are those of the steps, and the feed-forward inputs are `0`.
Hypotheses: system-identification offsets `0`, scale factors `1` (as
`rate_controller_target_reset` leaves them), `ATC_THR_G_BOOST = 0`, no motor limits, finite
feed-forward scalar, targets and gyro at most `8 rad/s`, PID states in `PIDRegion`. -/
theorem rate_controller_spec (hL : LibmSpec) (p : Params) (s : State) (o : Outputs) (inp : Inputs)
    (gr : RateGains p._pid_rate_roll kpRP kpRP kdRP 0)
    (gp : RateGains p._pid_rate_pitch kpRP kpRP kdRP 0)
    (gy : RateGains p._pid_rate_yaw kpY kiY 0 (5 / 2))
    (hgb : p._throttle_gain_boost.IsFinite) (hgb0 : p._throttle_gain_boost.toReal = 0)
    (hdt : s._dt_s.IsFinite) (hdtv : s._dt_s.toReal = dtR)
    (hpd : Ones s._pd_scale) (hi : Ones s._i_scale)
    (hsys : Zeros s._sysid_ang_vel_body_rads) (hact : Zeros s._actuator_sysid)
    (hffs : s._feedforward_scalar.IsFinite)
    (hlr : inp.limit_roll = false) (hlp : inp.limit_pitch = false) (hly : inp.limit_yaw = false)
    (hav : VBox8 s._ang_vel_body_rads) (hg : VBox8 inp.get_gyro_latest)
    (rr : PIDRegion s._pid_rate_roll) (rp : PIDRegion s._pid_rate_pitch)
    (ry : PIDRegion s._pid_rate_yaw) :
    let r := rate_controller_run p s o inp
    let av := s._ang_vel_body_rads
    let gy := inp.get_gyro_latest
    PIDStepSpec 1 kpRP kpRP kdRP s._pid_rate_roll._target.toReal s._pid_rate_roll._error.toReal
        s._pid_rate_roll._derivative.toReal s._pid_rate_roll._integrator.toReal av.x.toReal
        gy.x.toReal r.1._pid_rate_roll r.2.set_roll ∧
      PIDStepSpec 1 kpRP kpRP kdRP s._pid_rate_pitch._target.toReal
        s._pid_rate_pitch._error.toReal s._pid_rate_pitch._derivative.toReal
        s._pid_rate_pitch._integrator.toReal av.y.toReal gy.y.toReal r.1._pid_rate_pitch
        r.2.set_pitch ∧
      PIDStepSpec α2p5 kpY kiY 0 s._pid_rate_yaw._target.toReal s._pid_rate_yaw._error.toReal
        s._pid_rate_yaw._derivative.toReal s._pid_rate_yaw._integrator.toReal av.z.toReal
        gy.z.toReal r.1._pid_rate_yaw r.2.set_yaw ∧
      r.2.set_roll_ff.IsFinite ∧ r.2.set_roll_ff.toReal = 0 ∧
      r.2.set_pitch_ff.IsFinite ∧ r.2.set_pitch_ff.toReal = 0 ∧
      r.2.set_yaw_ff.IsFinite ∧ r.2.set_yaw_ff.toReal = 0 := by
  intro r av gyv
  obtain ⟨X, Y, eX⟩ := gain_boost_shape p s inp
  obtain ⟨m, em⟩ := rpy_mix_shape (update_throttle_gain_boost p s inp) inp
  have hX : Ones X := by have := gain_boost_pd hL p s inp hgb hgb0 hpd; rwa [eX] at this
  obtain ⟨e1, e2, e3, e4, e5, e6, e7, e8, e9⟩ := rate_run_eq p s o inp
  simp only [em] at e1 e2 e3 e4 e5 e6 e7 e8 e9
  simp only [eX] at e1 e2 e3 e4 e5 e6 e7 e8 e9
  obtain ⟨px, pxv, py, pyv, pz, pzv⟩ := hX
  obtain ⟨ix, ixv, iy, iyv, iz, izv⟩ := hi
  obtain ⟨sx, sxv, sy, syv, sz, szv⟩ := hsys
  obtain ⟨ax, axv, ay, ayv, az, azv⟩ := hact
  obtain ⟨vx, vxb, vy, vyb, vz, vzb⟩ := hav
  obtain ⟨gx, gxb, gy', gyb, gz, gzb⟩ := hg
  -- the targets: `ang_vel_body + sysid`, of the same values
  have tx := Float32.add_zero_val vx sx sxv
  have ty := Float32.add_zero_val vy sy syv
  have tz := Float32.add_zero_val vz sz szv
  obtain ⟨Rs, Rff⟩ := roll_pid_spec hL gr s._pid_rate_roll inp._pid_rate_roll _ _ _ _ _ hdt hdtv
    px pxv ix ixv rr.reset tx.1 gx rr.fT rr.fE rr.fD rr.fI (by rw [tx.2]; exact vxb) gxb rr.rT
    rr.rE rr.rD rr.rI
  obtain ⟨Ps, Pff⟩ := roll_pid_spec hL gp s._pid_rate_pitch inp._pid_rate_pitch _ _ _ _ _ hdt hdtv
    py pyv iy iyv rp.reset ty.1 gy' rp.fT rp.fE rp.fD rp.fI (by rw [ty.2]; exact vyb) gyb rp.rT
    rp.rE rp.rD rp.rI
  obtain ⟨Ys, Yff⟩ := yaw_pid_spec hL gy s._pid_rate_yaw inp._pid_rate_yaw _ _ _ _ _ hdt hdtv
    pz pzv iz izv ry.reset tz.1 gz ry.fT ry.fE ry.fD ry.fI (by rw [tz.2]; exact vzb) gzb ry.rT
    ry.rE ry.rD ry.rI
  rw [hlr] at e1 e4 e7
  rw [hlp] at e2 e5 e8
  rw [hly] at e3 e6 e9
  have ox := Float32.add_zero_val Rs.2.2.2.2.1 ax axv
  have oy := Float32.add_zero_val Ps.2.2.2.2.1 ay ayv
  have oz := Float32.add_zero_val Ys.2.2.2.2.1 az azv
  have fy := Float32.mul_exact Yff.1 hffs Yff.1 (by rw [Yff.2, zero_mul])
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [tx.2] at Rs; rw [e1, e4]; exact pidStep_congr_out Rs ox.1 ox.2
  · rw [ty.2] at Ps; rw [e2, e5]; exact pidStep_congr_out Ps oy.1 oy.2
  · rw [tz.2] at Ys; rw [e3, e6]; exact pidStep_congr_out Ys oz.1 oz.2
  · rw [e7]; exact Rff.1
  · rw [e7]; exact Rff.2
  · rw [e8]; exact Pff.1
  · rw [e8]; exact Pff.2
  · rw [e9]; exact fy.1
  · rw [e9]; exact fy.2.trans Yff.2

end Rate

end

end Contracts.Track.Att
