import FloatModel.Lit
import Contracts.Quick.Tilt

/-!
# Q2: the attitude controller's rate limiter

`Q2 rate_targets_bounded` as posed (the body-rate targets after any tick within
`ATC_RATE_R/P/Y_MAX`) is **false**: `AC_AttitudeControl::attitude_controller_run_quat` applies
`ang_vel_limit` to the attitude-error rate and *then* adds the feedforward, and above 30° of
thrust-angle error mixes the sampled gyro into the yaw target (`z := gyro.z * (1 - ff) + z * ff`,
and `z := gyro.z` above 60°). Counterexample in `QUICK.md` (`quick_cex q2c`: a 45° tilt and a
`10 rad/s` yaw-rate sample, inside the mission's sample envelope, give a yaw target of `5 rad/s`
against a limit of `30°/s`).

What is true is the limiter itself, `ang_vel_limit` (`AC_AttitudeControl.cpp:1206-1226`):

* `ang_vel_limit_z`: the yaw rate is within the yaw limit whenever the limit is not zero, for every
  input (NaN and `±∞` included): `constrain_value(z, -y, y)`;
* `ang_vel_limit_x_single`, `ang_vel_limit_y_single`: with one of the roll/pitch limits zero, the
  other axis is clamped the same way.

* `ang_vel_limit_xy`: with both roll and pitch limits non-zero the limiter scales the pair
  `(x/r, y/p)` by its `float` length when that exceeds `1`; for finite rates below `2^16` and finite
  limits below `2^20` the roll and pitch rates leave it within `|r| (1 + 2^-19) + 2^-50` and
  `|p| (1 + 2^-19) + 2^-50` (rounding core `flen_ge` of `Tilt.lean`). A NaN input gives a NaN
  length, which fails `length > 1` and passes unchanged: that branch needs finite inputs.

Q7: the limiter has no period argument; the statements hold for every `dt`.
-/

open Float.Model UnpackedFloat AC_Attitude_lib

namespace Contracts.Quick

set_option linter.unusedSimpArgs false

/-- The symmetric clamp `constrain_value_line(v, -m, m)` of the attitude controller is finite and
within `|m|` of `0` for every `v` (NaN and `±∞` included), for every finite `m` below
`maxFinite32 / 2` (`m` of either sign). -/
theorem cvl_sym_bound (v m : Float32) (l : UInt32) (hm : m.IsFinite)
    (hm2 : |m.toReal| ≤ maxFinite32 / 2) :
    (constrain_value_line_float v (-m) m l).IsFinite ∧
      |(constrain_value_line_float v (-m) m l).toReal| ≤ |m.toReal| := by
  have e : constrain_value_line_float v (-m) m l = Float32.cvl v (-m) m := rfl
  rw [e]
  have hnm : (-m).IsFinite := (Float32.isFinite_neg m).2 hm
  obtain ⟨h1, h2, h3⟩ := Float32.cvl_between Float32.two32 (amt := v) hnm hm
    (by rw [Float32.toReal_neg, abs_neg]; exact hm2) hm2
  rw [Float32.toReal_neg] at h2 h3
  refine ⟨h1, abs_le.2 ⟨?_, ?_⟩⟩
  · have : -|m.toReal| ≤ min (-m.toReal) m.toReal :=
      le_min (neg_le_neg (le_abs_self _)) (neg_abs_le _)
    linarith
  · have : max (-m.toReal) m.toReal ≤ |m.toReal| := max_le (neg_le_abs _) (le_abs_self _)
    linarith

/-- **Q2, yaw**: `ang_vel_limit` (`AC_AttitudeControl.cpp:1206-1226`) bounds the yaw rate by the yaw
limit whenever the limit is not zero, for every input (NaN and `±∞` included): its last step is
`constrain_value_line(z, -y, y)`. -/
theorem ang_vel_limit_z (e : Vector3f.State) (r p y : Float32) (hy0 : is_zero_float y = false)
    (hyf : y.IsFinite) (hyb : |y.toReal| ≤ maxFinite32 / 2) :
    (AC_AttitudeControl_Multi.ang_vel_limit e r p y).z.IsFinite ∧
      |(AC_AttitudeControl_Multi.ang_vel_limit e r p y).z.toReal| ≤ |y.toReal| := by
  unfold AC_AttitudeControl_Multi.ang_vel_limit
  simp only [id_run, id_pure, hy0, Bool.not_false, ite_true]
  split_ifs <;> (dsimp only; exact cvl_sym_bound _ _ _ hyf hyb)

/-- **Q2, roll with no pitch limit**: with a zero pitch limit, the roll rate is clamped to the
roll limit, for every input. -/
theorem ang_vel_limit_x_single (e : Vector3f.State) (r p y : Float32) (hr0 : is_zero_float r = false)
    (hp0 : is_zero_float p = true) (hrf : r.IsFinite) (hrb : |r.toReal| ≤ maxFinite32 / 2) :
    (AC_AttitudeControl_Multi.ang_vel_limit e r p y).x.IsFinite ∧
      |(AC_AttitudeControl_Multi.ang_vel_limit e r p y).x.toReal| ≤ |r.toReal| := by
  unfold AC_AttitudeControl_Multi.ang_vel_limit
  simp only [id_run, id_pure, hr0, hp0, Bool.not_false, Bool.not_true, ite_true, Bool.or_true,
    Bool.false_eq_true, ite_false]
  split <;> (dsimp only; exact cvl_sym_bound _ _ _ hrf hrb)

/-- **Q2, pitch with no roll limit**. -/
theorem ang_vel_limit_y_single (e : Vector3f.State) (r p y : Float32) (hr0 : is_zero_float r = true)
    (hp0 : is_zero_float p = false) (hpf : p.IsFinite) (hpb : |p.toReal| ≤ maxFinite32 / 2) :
    (AC_AttitudeControl_Multi.ang_vel_limit e r p y).y.IsFinite ∧
      |(AC_AttitudeControl_Multi.ang_vel_limit e r p y).y.toReal| ≤ |p.toReal| := by
  unfold AC_AttitudeControl_Multi.ang_vel_limit
  simp only [id_run, id_pure, hr0, hp0, Bool.not_false, Bool.not_true, ite_true, Bool.true_or,
    Bool.false_eq_true, ite_false]
  split <;> (dsimp only; exact cvl_sym_bound _ _ _ hpf hpb)

theorem avl_x_eq (e : Vector3f.State) (r p y : Float32) (hr0 : is_zero_float r = false)
    (hp0 : is_zero_float p = false) :
    (AC_AttitudeControl_Multi.ang_vel_limit e r p y).x =
      if Float32.sqrt ((e.x / r) * (e.x / r) + (e.y / p) * (e.y / p)) > 1.0 then
        e.x / r * r / Float32.sqrt ((e.x / r) * (e.x / r) + (e.y / p) * (e.y / p)) else e.x := by
  unfold AC_AttitudeControl_Multi.ang_vel_limit
  simp only [id_run, id_pure, hr0, hp0, Bool.or_false, Bool.false_eq_true, ite_false,
    Vector2f.length, norm_float2, sq_float, Vector2f.init_float2]
  split_ifs <;> rfl

theorem avl_y_eq (e : Vector3f.State) (r p y : Float32) (hr0 : is_zero_float r = false)
    (hp0 : is_zero_float p = false) :
    (AC_AttitudeControl_Multi.ang_vel_limit e r p y).y =
      if Float32.sqrt ((e.x / r) * (e.x / r) + (e.y / p) * (e.y / p)) > 1.0 then
        e.y / p * p / Float32.sqrt ((e.x / r) * (e.x / r) + (e.y / p) * (e.y / p)) else e.y := by
  unfold AC_AttitudeControl_Multi.ang_vel_limit
  simp only [id_run, id_pure, hr0, hp0, Bool.or_false, Bool.false_eq_true, ite_false,
    Vector2f.length, norm_float2, sq_float, Vector2f.init_float2]
  split_ifs <;> rfl

theorem f32_abs_unpack (a : Float32) : (Float32.abs a).toModel.unpack = a.toModel.unpack.abs := by
  have hc := a.canonicalIn_unpack
  have : CanonicalIn Format.binary32 a.toModel.unpack.abs := by
    cases h : a.toModel.unpack <;> simp_all [CanonicalIn, UnpackedFloat.abs]
  exact Float32.Model.unpack_pack_of_canonicalIn this

theorem f32_abs_toReal (a : Float32) : (Float32.abs a).toReal = |a.toReal| := by
  rw [Float32.toReal, f32_abs_unpack, Float32.toReal]
  cases a.toModel.unpack with
  | finite s m e hm =>
    cases s <;> simp [UnpackedFloat.abs, UnpackedFloat.toReal, Sign.apply, abs_mul]
  | _ => simp [UnpackedFloat.abs, UnpackedFloat.toReal]

theorem f32_abs_isFinite (a : Float32) : (Float32.abs a).IsFinite ↔ a.IsFinite := by
  rw [Float32.isFinite_iff, Float32.isFinite_iff, f32_abs_unpack]
  cases a.toModel.unpack <;> simp [UnpackedFloat.abs, UnpackedFloat.isFinite]

/-- A finite `float` that `is_zero` rejects has magnitude at least `2^-23`. -/
theorem abs_ge_of_not_zero {r : Float32} (hr : r.IsFinite) (h : is_zero_float r = false) :
    1 / 2 ^ 23 ≤ |r.toReal| := by
  have h' : ¬ (Float32.abs r < (1.1920929e-7 : Float32)) := by simpa [is_zero_float] using h
  rw [Float32.lt_iff_toReal_lt ((f32_abs_isFinite r).2 hr) isFinite_eps, f32_abs_toReal,
    toReal_eps] at h'
  exact not_lt.1 h'

theorem f32_lit_one_toReal : (1.0 : Float32).toReal = 1 := Float32.toReal_lit_one

/-- A `float` quotient of finite values, with its rounding bound in the form used below. -/
theorem fdiv {a b : Float32} (ha : a.IsFinite) (hb : b.IsFinite) (hb0 : b.toReal ≠ 0)
    (hq : |a.toReal / b.toReal| ≤ 2 ^ 100) :
    (a / b).IsFinite ∧ |(a / b).toReal - a.toReal / b.toReal| ≤
      |a.toReal / b.toReal| / 16777216 + 1 / 2 ^ 150 := by
  obtain ⟨f, e⟩ := Float32.div_err_all ha hb hb0 (hq.trans maxF_big)
  rw [u24, e150] at e
  exact ⟨f, by linarith⟩

theorem fmul {a b : Float32} (ha : a.IsFinite) (hb : b.IsFinite)
    (hq : |a.toReal * b.toReal| ≤ 2 ^ 100) :
    (a * b).IsFinite ∧ |(a * b).toReal - a.toReal * b.toReal| ≤
      |a.toReal * b.toReal| / 16777216 + 1 / 2 ^ 150 := by
  obtain ⟨f, e⟩ := Float32.mul_err_all ha hb (hq.trans maxF_big)
  rw [u24, e150] at e
  exact ⟨f, by linarith⟩

set_option maxHeartbeats 2000000 in
/-- The scaling step of `ang_vel_limit` on one axis: for a finite length `Lf` that bounds the
normalized rate `a / r` (`|a/r| ≤ Lf (1 + 2^-21) + 2^-74`), the output
`if Lf > 1 then (a/r)·r/Lf else a` (in `float`) is finite and within `|r| (1 + 2^-19) + 2^-50`, for
finite `a` below `2^16` and a finite limit with `2^-23 ≤ |r| ≤ 2^20`. -/
theorem rate_scale_bound {a r Lf : Float32} (ha : a.IsFinite) (hr : r.IsFinite) (fL : Lf.IsFinite)
    (ha' : |a.toReal| ≤ 2 ^ 16) (hr1 : 1 / 2 ^ 23 ≤ |r.toReal|) (hr2 : |r.toReal| ≤ 2 ^ 20)
    (hqN : |(a / r).toReal| ≤ Lf.toReal * (1 + 1 / 2 ^ 21) + 1 / 2 ^ 74) :
    (if Lf > 1.0 then a / r * r / Lf else a).IsFinite ∧
      |(if Lf > 1.0 then a / r * r / Lf else a).toReal| ≤
        |r.toReal| * (1 + 1 / 2 ^ 19) + 1 / 2 ^ 50 := by
  have hr0 : r.toReal ≠ 0 := fun h => by rw [h, abs_zero] at hr1; norm_num at hr1
  have hrpos : 0 < |r.toReal| := abs_pos.2 hr0
  have hq1b : |a.toReal / r.toReal| ≤ 2 ^ 39 := by
    rw [abs_div, div_le_iff₀ hrpos]
    calc |a.toReal| ≤ 2 ^ 16 := ha'
      _ = 2 ^ 39 * (1 / 2 ^ 23) := by norm_num
      _ ≤ 2 ^ 39 * |r.toReal| := by nlinarith
  obtain ⟨f1, e1⟩ := fdiv ha hr hr0 (hq1b.trans (by norm_num))
  have hq1 : |(a / r).toReal| ≤ 2 ^ 40 := by
    have := abs_sub_abs_le_abs_sub (a / r).toReal (a.toReal / r.toReal); linarith
  set L := Lf.toReal with hLd
  set q := (a / r).toReal with hqd
  by_cases hc : Lf > 1.0
  · rw [ite_eq_left hc]
    have hc' : (1.0 : Float32) < Lf := hc
    rw [Float32.lt_iff_toReal_lt Float32.isFinite_lit_one fL, f32_lit_one_toReal] at hc'
    have hL1 : 1 < L := hc'
    have hP : |q * r.toReal| ≤ 2 ^ 100 := by
      rw [abs_mul]
      have : |q| * |r.toReal| ≤ 2 ^ 40 * 2 ^ 20 := mul_le_mul hq1 hr2 (abs_nonneg _) (by positivity)
      linarith [show (2 : ℝ) ^ 40 * 2 ^ 20 ≤ 2 ^ 100 by norm_num]
    obtain ⟨fP, eP⟩ := fmul f1 hr hP
    set P := (a / r * r).toReal with hPd
    have hPabs : |P| ≤ |q| * |r.toReal| * (1 + 1 / 16777216) + 1 / 2 ^ 150 := by
      have := abs_sub_abs_le_abs_sub P (q * r.toReal)
      rw [abs_mul] at this eP; linarith
    have hLpos : 0 < L := by linarith
    have hD : |P / L| ≤ 2 ^ 100 := by
      rw [abs_div, abs_of_pos hLpos, div_le_iff₀ hLpos]
      have : |P| ≤ 2 ^ 61 := by
        have : |q| * |r.toReal| ≤ 2 ^ 40 * 2 ^ 20 :=
          mul_le_mul hq1 hr2 (abs_nonneg _) (by positivity)
        nlinarith
      nlinarith
    obtain ⟨fD, eD⟩ := fdiv fP fL hLpos.ne' hD
    refine ⟨fD, ?_⟩
    set D := (a / r * r / Lf).toReal
    have hDabs : |D| ≤ |P / L| * (1 + 1 / 16777216) + 1 / 2 ^ 150 := by
      have := abs_sub_abs_le_abs_sub D (P / L); linarith
    have hPL : |P / L| ≤ |P| := by
      rw [abs_div, abs_of_pos hLpos]; exact div_le_self (abs_nonneg _) hL1.le
    -- |P| / L ≤ c |r| (1+u) + τ |r| (1+u) + η
    have hPL2 : |P / L| ≤ (1 + 1 / 2 ^ 21) * |r.toReal| * (1 + 1 / 16777216) +
        1 / 2 ^ 74 * |r.toReal| * (1 + 1 / 16777216) + 1 / 2 ^ 150 := by
      rw [abs_div, abs_of_pos hLpos, div_le_iff₀ hLpos]
      have h1 : |q| * |r.toReal| ≤ (L * (1 + 1 / 2 ^ 21) + 1 / 2 ^ 74) * |r.toReal| :=
        mul_le_mul_of_nonneg_right hqN (abs_nonneg _)
      have hrn := abs_nonneg r.toReal
      nlinarith
    have hfin : ((1 + 1 / 2 ^ 21) * |r.toReal| * (1 + 1 / 16777216) +
        1 / 2 ^ 74 * |r.toReal| * (1 + 1 / 16777216) + 1 / 2 ^ 150) * (1 + 1 / 16777216) +
          1 / 2 ^ 150 ≤ |r.toReal| * (1 + 1 / 2 ^ 19) + 1 / 2 ^ 50 := by
      nlinarith [abs_nonneg r.toReal]
    nlinarith
  · rw [ite_eq_right hc]
    refine ⟨ha, ?_⟩
    have hc' : ¬ (1.0 : Float32) < Lf := hc
    rw [Float32.lt_iff_toReal_lt Float32.isFinite_lit_one fL, f32_lit_one_toReal] at hc'
    have hL1 : L ≤ 1 := not_lt.1 hc'
    have hqa : |a.toReal / r.toReal| * (1 - 1 / 16777216) ≤ |q| + 1 / 2 ^ 150 := by
      have := abs_sub_abs_le_abs_sub (a.toReal / r.toReal) q
      rw [abs_sub_comm] at this; linarith
    have hq3 : |q| ≤ (1 + 1 / 2 ^ 21) + 1 / 2 ^ 74 := by nlinarith
    rw [abs_div] at hqa
    have hk : |a.toReal| / |r.toReal| * (1 - 1 / 16777216) ≤ (1 + 1 / 2 ^ 21) + 2 / 2 ^ 74 := by
      linarith [show (1 : ℝ) / 2 ^ 150 ≤ 1 / 2 ^ 74 by norm_num]
    have : |a.toReal| * (1 - 1 / 16777216) ≤ ((1 + 1 / 2 ^ 21) + 2 / 2 ^ 74) * |r.toReal| := by
      have := mul_le_mul_of_nonneg_right hk (abs_nonneg r.toReal)
      rwa [show |a.toReal| / |r.toReal| * (1 - 1 / 16777216) * |r.toReal| =
        |a.toReal| * (1 - 1 / 16777216) by field_simp] at this
    nlinarith [abs_nonneg r.toReal]

/-- **Q2, roll and pitch with both limits non-zero** (`ang_vel_limit`, the scaling branch): for
finite rates below `2^16` and finite limits below `2^20` (not `is_zero`), the roll and pitch rates
leave the limiter within `|roll limit| (1 + 2^-19) + 2^-50` and `|pitch limit| (1 + 2^-19) +
2^-50`. A NaN rate makes the length NaN, which fails `length > 1` and passes unchanged: the
finiteness hypothesis is needed. -/
theorem ang_vel_limit_xy (e : Vector3f.State) (r p y : Float32) (hx : e.x.IsFinite)
    (hy : e.y.IsFinite) (hr : r.IsFinite) (hp : p.IsFinite) (hx' : |e.x.toReal| ≤ 2 ^ 16)
    (hy' : |e.y.toReal| ≤ 2 ^ 16) (hr0 : is_zero_float r = false) (hp0 : is_zero_float p = false)
    (hr2 : |r.toReal| ≤ 2 ^ 20) (hp2 : |p.toReal| ≤ 2 ^ 20) :
    (AC_AttitudeControl_Multi.ang_vel_limit e r p y).x.IsFinite ∧
      |(AC_AttitudeControl_Multi.ang_vel_limit e r p y).x.toReal| ≤
        |r.toReal| * (1 + 1 / 2 ^ 19) + 1 / 2 ^ 50 ∧
    (AC_AttitudeControl_Multi.ang_vel_limit e r p y).y.IsFinite ∧
      |(AC_AttitudeControl_Multi.ang_vel_limit e r p y).y.toReal| ≤
        |p.toReal| * (1 + 1 / 2 ^ 19) + 1 / 2 ^ 50 := by
  have hr1 := abs_ge_of_not_zero hr hr0
  have hp1 := abs_ge_of_not_zero hp hp0
  have hr00 : r.toReal ≠ 0 := fun h => by rw [h, abs_zero] at hr1; norm_num at hr1
  have hp00 : p.toReal ≠ 0 := fun h => by rw [h, abs_zero] at hp1; norm_num at hp1
  -- the normalized rates are finite and below `2^40`
  have nb : ∀ {a q : Float32}, a.IsFinite → q.IsFinite → |a.toReal| ≤ 2 ^ 16 →
      1 / 2 ^ 23 ≤ |q.toReal| → (a / q).IsFinite ∧ |(a / q).toReal| ≤ 2 ^ 40 := by
    intro a q ha hq ha' hq1
    have hq0 : q.toReal ≠ 0 := fun h => by rw [h, abs_zero] at hq1; norm_num at hq1
    have hb : |a.toReal / q.toReal| ≤ 2 ^ 39 := by
      rw [abs_div, div_le_iff₀ (abs_pos.2 hq0)]
      calc |a.toReal| ≤ 2 ^ 16 := ha'
        _ = 2 ^ 39 * (1 / 2 ^ 23) := by norm_num
        _ ≤ 2 ^ 39 * |q.toReal| := by nlinarith
    obtain ⟨f, e⟩ := fdiv ha hq hq0 (hb.trans (by norm_num))
    refine ⟨f, ?_⟩
    have := abs_sub_abs_le_abs_sub (a / q).toReal (a.toReal / q.toReal); linarith
  obtain ⟨f1, b1⟩ := nb hx hr hx' hr1
  obtain ⟨f2, b2⟩ := nb hy hp hy' hp1
  obtain ⟨fL, hL0, -, hN⟩ := flen_ge f1 f2 b1 b2
  have hNq := N2_le_of_sq (by positivity) hN
  obtain ⟨hq1, hq2⟩ := abs_le_N2 (e.x / r).toReal (e.y / p).toReal
  rw [avl_x_eq e r p y hr0 hp0, avl_y_eq e r p y hr0 hp0]
  obtain ⟨g1, k1⟩ := rate_scale_bound hx hr fL hx' hr1 hr2 (hq1.trans hNq)
  obtain ⟨g2, k2⟩ := rate_scale_bound hy hp fL hy' hp1 hp2 (hq2.trans hNq)
  exact ⟨g1, k1, g2, k2⟩

end Contracts.Quick
