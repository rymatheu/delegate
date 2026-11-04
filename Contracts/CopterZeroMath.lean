import Contracts.CopterZero
import AC_PID.AC_PID
import AC_AttitudeControl.AC_AttitudeControl

/-!
# Zero lemmas for `AP_Math/control` and `AC_PID`

`AC_PID.update_all` at a zero target, a zero measurement and a zero state (`pid_update_all_Z`);
`sqrt_controller` at a zero error (`sqrt_controller_Z`); `sqrt_controller_accel` at a zero command
(`sqrt_controller_accel_Z`); `shape_accel`, `shape_pos_vel_accel`, `shape_angle_vel_accel` at zero
error and zero rate state (`shape_accel_Z`, `shape_pos_vel_accel_Z`, `shape_angle_vel_accel_Z`).

Finiteness is not enough for these functions: their branch conditions compare a zero with
derived quantities such as `second_ord_lim / sq(p)`, and a product of two finite floats can
overflow. The parameters are therefore bounded (`|p| ≤ 10¹⁸`, ...); every bound is far beyond any
ArduPilot parameter range, and the guards `is_positive`/`is_zero` give the lower bounds `2⁻²³`.
-/

open Float.Model UnpackedFloat AP_Math

namespace Contracts.CopterZero

/-! ## Real bounds and the bracket, binary32 -/

theorem maxFinite32_ge : (1e38 : ℝ) ≤ maxFinite32 := by
  unfold maxFinite32
  rw [show (104 : ℤ) = ((104 : ℕ) : ℤ) from rfl, zpow_natCast]; norm_num

theorem eps_eq : (2 : ℝ) ^ (-23 : ℤ) = 1 / 8388608 := by rw [zpow_neg]; norm_num

theorem fin_add {a b : Float32} (ha : a.IsFinite) (hb : b.IsFinite)
    (h : |a.toReal + b.toReal| ≤ 1e38) : (a + b).IsFinite :=
  (Float32.add_err_all ha hb (h.trans maxFinite32_ge)).1
theorem fin_sub {a b : Float32} (ha : a.IsFinite) (hb : b.IsFinite)
    (h : |a.toReal - b.toReal| ≤ 1e38) : (a - b).IsFinite :=
  (Float32.sub_err_all ha hb (h.trans maxFinite32_ge)).1
theorem fin_mul {a b : Float32} (ha : a.IsFinite) (hb : b.IsFinite)
    (h : |a.toReal * b.toReal| ≤ 1e38) : (a * b).IsFinite :=
  (Float32.mul_err_all ha hb (h.trans maxFinite32_ge)).1
theorem fin_div {a b : Float32} (ha : a.IsFinite) (hb : b.IsFinite) (hb0 : b.toReal ≠ 0)
    (h : |a.toReal / b.toReal| ≤ 1e38) : (a / b).IsFinite :=
  (Float32.div_err_all ha hb hb0 (h.trans maxFinite32_ge)).1

theorem ge_add {a b f : Float32} (ha : a.IsFinite) (hb : b.IsFinite) (hf : f.IsFinite)
    (h : |a.toReal + b.toReal| ≤ 1e38) (hle : f.toReal ≤ a.toReal + b.toReal) :
    f.toReal ≤ (a + b).toReal :=
  (Float32.add_bracket ha hb (h.trans maxFinite32_ge) hf).1 hle
theorem ge_mul {a b f : Float32} (ha : a.IsFinite) (hb : b.IsFinite) (hf : f.IsFinite)
    (h : |a.toReal * b.toReal| ≤ 1e38) (hle : f.toReal ≤ a.toReal * b.toReal) :
    f.toReal ≤ (a * b).toReal :=
  (Float32.mul_bracket ha hb (h.trans maxFinite32_ge) hf).1 hle
theorem le_mul {a b f : Float32} (ha : a.IsFinite) (hb : b.IsFinite) (hf : f.IsFinite)
    (h : |a.toReal * b.toReal| ≤ 1e38) (hle : a.toReal * b.toReal ≤ f.toReal) :
    (a * b).toReal ≤ f.toReal :=
  (Float32.mul_bracket ha hb (h.trans maxFinite32_ge) hf).2 hle
theorem ge_div {a b f : Float32} (ha : a.IsFinite) (hb : b.IsFinite) (hb0 : b.toReal ≠ 0)
    (hf : f.IsFinite) (h : |a.toReal / b.toReal| ≤ 1e38) (hle : f.toReal ≤ a.toReal / b.toReal) :
    f.toReal ≤ (a / b).toReal :=
  (Float32.div_bracket ha hb hb0 (h.trans maxFinite32_ge) hf).1 hle

theorem nonneg_mul {a b : Float32} (ha : a.IsFinite) (hb : b.IsFinite)
    (h : |a.toReal * b.toReal| ≤ 1e38) (h0 : 0 ≤ a.toReal * b.toReal) : 0 ≤ (a * b).toReal := by
  have := ge_mul ha hb Float32.isFinite_zero h (by rw [Float32.toReal_zero]; exact h0)
  rwa [Float32.toReal_zero] at this
theorem nonpos_mul {a b : Float32} (ha : a.IsFinite) (hb : b.IsFinite)
    (h : |a.toReal * b.toReal| ≤ 1e38) (h0 : a.toReal * b.toReal ≤ 0) : (a * b).toReal ≤ 0 := by
  have := le_mul ha hb Float32.isFinite_zero h (by rw [Float32.toReal_zero]; exact h0)
  rwa [Float32.toReal_zero] at this
theorem nonneg_div {a b : Float32} (ha : a.IsFinite) (hb : b.IsFinite) (hb0 : b.toReal ≠ 0)
    (h : |a.toReal / b.toReal| ≤ 1e38) (h0 : 0 ≤ a.toReal / b.toReal) : 0 ≤ (a / b).toReal := by
  have := ge_div ha hb hb0 Float32.isFinite_zero h (by rw [Float32.toReal_zero]; exact h0)
  rwa [Float32.toReal_zero] at this

theorem bool_or_false {a b : Bool} (h : ¬ (a || b) = true) : a = false ∧ b = false := by
  cases a <;> cases b <;> simp_all

theorem bool_not_true {a : Bool} (h : ¬ a = true) : a = false := by cases a <;> simp_all

/-! ## `calc_lowpass_alpha_dt` is finite -/

/-- The low-pass coefficient `calc_lowpass_alpha_dt dt cutoff` is finite for finite arguments of
magnitude at most `10³⁰` (in the computed branch it lies in `[0, 1]`). -/
theorem alpha_fin {dt c : Float32} (hdt : dt.IsFinite) (hc : c.IsFinite)
    (hdtb : |dt.toReal| ≤ 1e30) (hcb : |c.toReal| ≤ 1e30) :
    (calc_lowpass_alpha_dt dt c).IsFinite := by
  unfold calc_lowpass_alpha_dt
  split_ifs with h1 h2 h3
  · exact lit_one.1
  · exact lit_one.1
  · exact Z_lit0.1
  · obtain ⟨hdn, hcn⟩ := bool_or_false h1
    have hc0 := pos_of_not_neg_not_zero hc hcn (bool_not_true h2)
    have hd0 := pos_of_not_neg_not_zero hdt hdn (bool_not_true h3)
    rw [eps_eq] at hc0 hd0
    obtain ⟨hMf, hMlo, hMhi⟩ := M_2PI_spec
    have hcb' := abs_le.1 hcb
    have hdb' := abs_le.1 hdtb
    have hmb : |M_2PI.toReal * c.toReal| ≤ 1e38 := by
      rw [abs_le]; constructor <;> nlinarith
    have hm := fin_mul hMf hc hmb
    have hmc : c.toReal ≤ (M_2PI * c).toReal := ge_mul hMf hc hc hmb (by nlinarith)
    have hmpos : 0 < (M_2PI * c).toReal := by linarith
    have hrb : |(1.0 : Float32).toReal / (M_2PI * c).toReal| ≤ 1e38 := by
      rw [lit_one.2, abs_div, abs_one, abs_of_pos hmpos, div_le_iff₀ hmpos]; nlinarith
    have hr := fin_div lit_one.1 hm hmpos.ne' hrb
    have hr0 : 0 ≤ ((1.0 : Float32) / (M_2PI * c)).toReal :=
      nonneg_div lit_one.1 hm hmpos.ne' hrb (by rw [lit_one.2]; exact div_nonneg zero_le_one hmpos.le)
    have hr1 : ((1.0 : Float32) / (M_2PI * c)).toReal ≤ 1e8 := by
      have := (abs_le.1 (Float32.div_err_all lit_one.1 hm hmpos.ne' (hrb.trans maxFinite32_ge)).2)
      rw [lit_one.2] at this
      have h1m : 1 / (M_2PI * c).toReal ≤ 8388608 := by
        rw [div_le_iff₀ hmpos]; nlinarith
      have h24 : (2 : ℝ) ^ (-24 : ℤ) ≤ 1 := zpow_le_one_of_nonpos₀ one_le_two (by norm_num)
      have h150 : (2 : ℝ) ^ (-150 : ℤ) ≤ 1 := zpow_le_one_of_nonpos₀ one_le_two (by norm_num)
      have hpos : 0 ≤ 1 / (M_2PI * c).toReal := div_nonneg zero_le_one hmpos.le
      rw [abs_of_nonneg hpos] at this
      have hx := this.2
      have hm2 : (2 : ℝ) ^ (-24 : ℤ) * (1 / (M_2PI * c).toReal) ≤ 1 * 8388608 :=
        mul_le_mul h24 h1m hpos zero_le_one
      linarith
    have hsb : |dt.toReal + ((1.0 : Float32) / (M_2PI * c)).toReal| ≤ 1e38 := by
      rw [abs_le]; constructor <;> linarith
    have hs := fin_add hdt hr hsb
    have hsd : dt.toReal ≤ (dt + (1.0 : Float32) / (M_2PI * c)).toReal :=
      ge_add hdt hr hdt hsb (by linarith)
    have hspos : 0 < (dt + (1.0 : Float32) / (M_2PI * c)).toReal := by linarith
    refine fin_div hdt hs hspos.ne' ?_
    rw [abs_div, abs_of_pos hspos, abs_of_pos (by linarith), div_le_iff₀ hspos]; nlinarith

/-! ## `AC_PID` -/

/-- PID memory at zero: integrator, filtered target, filtered error, derivative and target
derivative are zeros. -/
def ZPID (s : AC_PID.State) : Prop :=
  Z s._integrator ∧ Z s._target ∧ Z s._error ∧ Z s._derivative ∧ Z s._target_derivative

/-- Finite gains, a non-negative integrator limit, and filter frequencies of magnitude at most
`10³⁰`. -/
structure PidOK (p : AC_PID.Params) : Prop where
  P : p.P.IsFinite
  I : p.I.IsFinite
  D : p.D.IsFinite
  FF : p.FF.IsFinite
  IMAX : p.IMAX.IsFinite
  IMAX0 : 0 ≤ p.IMAX.toReal
  PDMX : p.PDMX.IsFinite
  D_FF : p.D_FF.IsFinite
  FLTT : p.FLTT.IsFinite
  FLTE : p.FLTE.IsFinite
  FLTD : p.FLTD.IsFinite
  FLTTb : |p.FLTT.toReal| ≤ 1e30
  FLTEb : |p.FLTE.toReal| ≤ 1e30
  FLTDb : |p.FLTD.toReal| ≤ 1e30

/-- `update_i` keeps the zero memory. -/
theorem update_i_Z (p : AC_PID.Params) (hp : PidOK p) {s : AC_PID.State} (hs : ZPID s)
    {dt : Float32} (hdt : dt.IsFinite) (limit : Bool) {i_scale : Float32}
    (hi : i_scale.IsFinite) : ZPID (AC_PID.update_i p s dt limit i_scale) := by
  unfold AC_PID.update_i
  have hint : Z (constrain_float (s._integrator + s._error * p.I * i_scale * dt) (-p.IMAX) p.IMAX) :=
    constrain_Z (Z_add hs.1 (Z_mul_left (Z_mul_left (Z_mul_left hs.2.2.1 hp.I) hi) hdt))
      ((Float32.isFinite_neg _).2 hp.IMAX) hp.IMAX (by rw [Float32.toReal_neg]; linarith [hp.IMAX0])
      hp.IMAX0
  split_ifs
  · exact ⟨hint, hs.2⟩
  · exact hs
  · exact ⟨Z_lit0, hs.2⟩

theorem slew_one (a b : Float32) : AC_PID.slew_limiter_modifier_smax_off a b = 1.0 := rfl

/-- The common tail of `update_all` after `update_i`. -/
theorem pid_tail_Z (p : AC_PID.Params) (hp : PidOK p) {s1 : AC_PID.State} (hs1 : ZPID s1)
    {pd : Float32} (hpd : pd.IsFinite) :
    Z (s1._error * p.P * 1.0 * pd + s1._derivative * p.D * 1.0 * pd + s1._integrator) ∧
      Z (s1._error * p.P * 1.0 * pd) ∧ Z (s1._derivative * p.D * 1.0 * pd) ∧
      Z (s1._target * p.FF + s1._target_derivative * p.D_FF) := by
  have hP : Z (s1._error * p.P * 1.0 * pd) :=
    Z_mul_left (Z_mul_left (Z_mul_left hs1.2.2.1 hp.P) lit_one.1) hpd
  have hD : Z (s1._derivative * p.D * 1.0 * pd) :=
    Z_mul_left (Z_mul_left (Z_mul_left hs1.2.2.2.1 hp.D) lit_one.1) hpd
  exact ⟨Z_add (Z_add hP hD) hs1.1, hP, hD,
    Z_add (Z_mul_left hs1.2.1 hp.FF) (Z_mul_left hs1.2.2.2.2 hp.D_FF)⟩

/-- The PD-sum limit is not active at zero: `|P + D| > PDMX` is false for `PDMX ≥ 2⁻²³`. -/
theorem pdmx_not {p : AC_PID.Params} (hp : PidOK p) (h : is_positive p.PDMX = true) {x : Float32}
    (hx : Z x) : ¬ (Float32.abs x > p.PDMX) := by
  have h0 := is_positive_ge hp.PDMX h
  have ha := Z_abs hx
  show ¬ p.PDMX < x.abs
  rw [lt_iff hp.PDMX ha.1, ha.2]
  linarith [eps_pos]

/-- **`AC_PID::update_all` at zero.** With a zero target, a zero measurement and the PID memory at
zero, the output is a zero, the memory stays at zero, and the feed-forward `get_ff` is a zero; for
every finite `dt` of magnitude at most `10³⁰`, every `limit`, and finite `pd_scale`, `i_scale`. -/
theorem pid_update_all_Z (p : AC_PID.Params) (hp : PidOK p) {s : AC_PID.State} (hs : ZPID s)
    {target measurement dt : Float32} (ht : Z target) (hm : Z measurement) (hdt : dt.IsFinite)
    (hdtb : |dt.toReal| ≤ 1e30) (limit : Bool) {pd_scale i_scale : Float32}
    (hpd : pd_scale.IsFinite) (hi : i_scale.IsFinite) :
    ZPID (AC_PID.update_all p s target measurement dt limit pd_scale i_scale).1 ∧
      Z (AC_PID.update_all p s target measurement dt limit pd_scale i_scale).2 ∧
      Z (AC_PID.get_ff (AC_PID.update_all p s target measurement dt limit pd_scale i_scale).1) := by
  have hT : (AC_PID.get_filt_T_alpha p dt).IsFinite := alpha_fin hdt hp.FLTT hdtb hp.FLTTb
  have hE : (AC_PID.get_filt_E_alpha p dt).IsFinite := alpha_fin hdt hp.FLTE hdtb hp.FLTEb
  have hD : (AC_PID.get_filt_D_alpha p dt).IsFinite := alpha_fin hdt hp.FLTD hdtb hp.FLTDb
  have hfin : (!target.isFinite || !measurement.isFinite) = false := by
    simp [show target.isFinite = true from ht.1, show measurement.isFinite = true from hm.1]
  unfold AC_PID.update_all
  simp only [Id.run, pure, hfin, Bool.false_eq_true, if_false, slew_one]
  split
  · -- `_reset_filter`: the filters restart at the inputs
    have hU := update_i_Z p hp (s := { s with
        _flags := { s._flags with _reset_filter := false },
        _target := target, _error := target - measurement,
        _derivative := 0.0, _target_derivative := 0.0 })
      ⟨hs.1, ht, Z_sub ht hm, Z_lit0, Z_lit0⟩ hdt limit hi
    generalize AC_PID.update_i p _ dt limit i_scale = s1 at hU ⊢
    obtain ⟨h1, hP, hD', hF⟩ := pid_tail_Z p hp hU hpd
    by_cases hx : is_positive p.PDMX = true
    · have hy := pdmx_not hp hx (Z_add hP hD')
      simp only [hx, hy, if_true, if_false]; exact ⟨hU, h1, hF⟩
    · rw [if_neg hx]; exact ⟨hU, h1, hF⟩
  · -- filtered update
    have hTg : Z (s._target + AC_PID.get_filt_T_alpha p dt * (target - s._target)) :=
      Z_add hs.2.1 (Z_mul_right hT (Z_sub ht hs.2.1))
    have hEr : Z (s._error + AC_PID.get_filt_E_alpha p dt *
        (s._target + AC_PID.get_filt_T_alpha p dt * (target - s._target) - measurement - s._error)) :=
      Z_add hs.2.2.1 (Z_mul_right hE (Z_sub (Z_sub hTg hm) hs.2.2.1))
    split
    · rename_i hpos
      have hdt0 := is_positive_ge hdt hpos
      have hdtne : dt.toReal ≠ 0 := by linarith [eps_pos]
      have hU := update_i_Z p hp (s := { s with
          _target := s._target + AC_PID.get_filt_T_alpha p dt * (target - s._target),
          _error := s._error + AC_PID.get_filt_E_alpha p dt *
            (s._target + AC_PID.get_filt_T_alpha p dt * (target - s._target) - measurement - s._error),
          _derivative := s._derivative + AC_PID.get_filt_D_alpha p dt *
            ((s._error + AC_PID.get_filt_E_alpha p dt *
              (s._target + AC_PID.get_filt_T_alpha p dt * (target - s._target) - measurement -
                s._error) - s._error) / dt - s._derivative),
          _target_derivative := (s._target + AC_PID.get_filt_T_alpha p dt * (target - s._target) -
            s._target) / dt })
        ⟨hs.1, hTg, hEr,
          Z_add hs.2.2.2.1 (Z_mul_right hD (Z_sub (Z_div (Z_sub hEr hs.2.2.1) hdt hdtne) hs.2.2.2.1)),
          Z_div (Z_sub hTg hs.2.1) hdt hdtne⟩ hdt limit hi
      generalize AC_PID.update_i p _ dt limit i_scale = s1 at hU ⊢
      obtain ⟨h1, hP, hD', hF⟩ := pid_tail_Z p hp hU hpd
      by_cases hx : is_positive p.PDMX = true
      · have hy := pdmx_not hp hx (Z_add hP hD')
        simp only [hx, hy, if_true, if_false]; exact ⟨hU, h1, hF⟩
      · rw [if_neg hx]; exact ⟨hU, h1, hF⟩
    · have hU := update_i_Z p hp (s := { s with
          _target := s._target + AC_PID.get_filt_T_alpha p dt * (target - s._target),
          _error := s._error + AC_PID.get_filt_E_alpha p dt *
            (s._target + AC_PID.get_filt_T_alpha p dt * (target - s._target) - measurement - s._error),
          _derivative := s._derivative, _target_derivative := s._target_derivative })
        ⟨hs.1, hTg, hEr, hs.2.2.2.1, hs.2.2.2.2⟩ hdt limit hi
      generalize AC_PID.update_i p _ dt limit i_scale = s1 at hU ⊢
      obtain ⟨h1, hP, hD', hF⟩ := pid_tail_Z p hp hU hpd
      by_cases hx : is_positive p.PDMX = true
      · have hy := pdmx_not hp hx (Z_add hP hD')
        simp only [hx, hy, if_true, if_false]; exact ⟨hU, h1, hF⟩
      · rw [if_neg hx]; exact ⟨hU, h1, hF⟩

/-! ## Helpers for the shaping functions -/

theorem abs_ge_of_not_zero {x : Float32} (hx : x.IsFinite) (h : is_zero x = false) :
    2 ^ (-23 : ℤ) ≤ |x.toReal| := by
  unfold is_zero at h
  rw [decide_eq_false_iff_not, lt_iff ((isFinite_abs x).2 hx) FLT_EPSILON_spec.1, toReal_abs,
    FLT_EPSILON_spec.2] at h
  exact not_lt.1 h

theorem div_abs_le {a b : Float32} (ha : a.IsFinite) (hb : b.IsFinite) (hb0 : b.toReal ≠ 0)
    (h : |a.toReal / b.toReal| ≤ 1e38) :
    (a / b).IsFinite ∧ |(a / b).toReal| ≤ 2 * |a.toReal / b.toReal| + 1 ∧
      (0 ≤ a.toReal / b.toReal → (1 / 2) * (a.toReal / b.toReal) - 1e-40 ≤ (a / b).toReal) := by
  obtain ⟨hf, he⟩ := Float32.div_err_all ha hb hb0 (h.trans maxFinite32_ge)
  have h24 : (2 : ℝ) ^ (-24 : ℤ) ≤ 1 / 2 := by rw [zpow_neg]; norm_num
  have h150 : (2 : ℝ) ^ (-150 : ℤ) ≤ 1e-40 := by rw [zpow_neg]; norm_num
  have hx := abs_nonneg (a.toReal / b.toReal)
  have hm : (2 : ℝ) ^ (-24 : ℤ) * |a.toReal / b.toReal| ≤ (1 / 2) * |a.toReal / b.toReal| :=
    mul_le_mul_of_nonneg_right h24 hx
  refine ⟨hf, ?_, ?_⟩
  · have := abs_sub_abs_le_abs_sub (a / b).toReal (a.toReal / b.toReal)
    linarith
  · intro h0
    have := (abs_le.1 he).1
    rw [abs_of_nonneg h0] at hm this; linarith

/-- `MAX v m = v` for a zero `v` and `m ≤ -2⁻²³`. -/
theorem MAX_Z_left {v m : Float32} (hv : Z v) (hm : m.IsFinite) (h : is_negative m = true) :
    MAX v m = v := by
  have := is_negative_le hm h
  rw [MAX_eq, if_pos]
  show m < v
  rw [lt_iff hm hv.1, hv.2]; linarith [eps_pos]

/-- `MIN v m = v` for a zero `v` and `m ≥ 2⁻²³`. -/
theorem MIN_Z_left {v m : Float32} (hv : Z v) (hm : m.IsFinite) (h : is_positive m = true) :
    MIN v m = v := by
  have := is_positive_ge hm h
  rw [MIN_eq, if_pos]
  rw [lt_iff hv.1 hm, hv.2]; linarith [eps_pos]

/-- `FLT_EPSILON²`, a float of value `2⁻⁴⁶`. -/
theorem eps2_spec : (FLT_EPSILON * FLT_EPSILON).IsFinite ∧
    (FLT_EPSILON * FLT_EPSILON).toReal = (2 ^ (-23 : ℤ)) * (2 ^ (-23 : ℤ)) := by
  obtain ⟨h1, h2⟩ := litPos (x := FLT_EPSILON * FLT_EPSILON) (m := 8388608) (e := -69)
    (hm := by decide) (by rfl)
  refine ⟨h1, h2.trans ?_⟩
  rw [eps_eq, zpow_neg]; norm_num

/-- `second_ord_lim / sq(p)` is finite and non-negative for `p` away from zero and bounded. -/
theorem linear_dist_nonneg {p sol : Float32} (hp : p.IsFinite) (hs : sol.IsFinite)
    (hpb : |p.toReal| ≤ 1e19) (hsb : |sol.toReal| ≤ 1e18) (hp0 : 2 ^ (-23 : ℤ) ≤ |p.toReal|)
    (hs0 : 0 ≤ sol.toReal) : (sol / sq p).IsFinite ∧ 0 ≤ (sol / sq p).toReal := by
  have he := eps_pos
  have hpp : p.toReal * p.toReal = |p.toReal| * |p.toReal| := by
    rw [← abs_mul, abs_of_nonneg (mul_self_nonneg _)]
  have hb : |p.toReal * p.toReal| ≤ 1e38 := by
    rw [abs_of_nonneg (mul_self_nonneg _), hpp]; nlinarith [abs_nonneg p.toReal]
  have hf : (sq p).IsFinite := fin_mul hp hp hb
  have hlo : (2 ^ (-23 : ℤ)) * (2 ^ (-23 : ℤ)) ≤ (sq p).toReal := by
    have := ge_mul hp hp eps2_spec.1 hb (by rw [eps2_spec.2, hpp]; nlinarith)
    rwa [eps2_spec.2] at this
  have hpos : 0 < (sq p).toReal := lt_of_lt_of_le (by positivity) hlo
  have hq : |sol.toReal / (sq p).toReal| ≤ 1e38 := by
    rw [abs_div, abs_of_pos hpos, div_le_iff₀ hpos]
    rw [eps_eq] at hlo
    nlinarith
  exact ⟨fin_div hs hf hpos.ne' hq, nonneg_div hs hf hpos.ne' hq (div_nonneg hs0 hpos.le)⟩

/-- The final clamp of `sqrt_controller` keeps a zero. -/
theorem sqrt_clamp_Z {x error dt : Float32} (hx : Z x) (he : Z error) (hdt : dt.IsFinite) :
    Z (if is_positive dt = true then constrain_float x (-error.abs / dt) (error.abs / dt) else x) := by
  split
  · rename_i h
    have h0 := is_positive_ge hdt h
    have hne : dt.toReal ≠ 0 := by linarith [eps_pos]
    have h1 := Z_div (Z_neg (Z_abs he)) hdt hne
    have h2 := Z_div (Z_abs he) hdt hne
    exact constrain_Z hx h1.1 h2.1 h1.2.le h2.2.ge
  · exact hx

/-! ## `sqrt_controller`, `sqrt_controller_accel` -/

/-- **`sqrt_controller` at zero error** is a zero, for finite `p`, `second_ord_lim`, `dt` with
`|p| ≤ 10¹⁹`, `|second_ord_lim| ≤ 10¹⁸`. In the square-root branch the comparisons `error > linear_dist`
and `error < -linear_dist` are false because `linear_dist = second_ord_lim / p² ≥ 0`. -/
theorem sqrt_controller_Z {error p sol dt : Float32} (he : Z error) (hp : p.IsFinite)
    (hs : sol.IsFinite) (hdt : dt.IsFinite) (hpb : |p.toReal| ≤ 1e19) (hsb : |sol.toReal| ≤ 1e18) :
    Z (sqrt_controller error p sol dt) := by
  unfold sqrt_controller
  simp only [is_positive_Z he, is_negative_Z he, Bool.false_eq_true, if_false]
  by_cases c0 : (is_negative sol || is_zero sol) = true
  · simp only [c0, if_true]; exact sqrt_clamp_Z (Z_mul_left he hp) he hdt
  · simp only [c0, Bool.false_eq_true, if_false]
    by_cases c1 : is_zero p = true
    · simp only [c1, if_true]; exact sqrt_clamp_Z Z_lit0 he hdt
    · simp only [c1, Bool.false_eq_true, if_false]
      obtain ⟨hsn, hsz⟩ := bool_or_false c0
      have hs0 := pos_of_not_neg_not_zero hs hsn hsz
      have hp0 := abs_ge_of_not_zero hp (bool_not_true c1)
      obtain ⟨hlf, hl0⟩ := linear_dist_nonneg hp hs hpb hsb hp0 (le_trans eps_pos.le hs0)
      have c4 : ¬ (error > sol / sq p) := by
        show ¬ (sol / sq p < error)
        rw [lt_iff hlf he.1, he.2]; linarith
      have c5 : ¬ (error < -(sol / sq p)) := by
        rw [lt_iff he.1 ((Float32.isFinite_neg _).2 hlf), he.2, Float32.toReal_neg]; linarith
      simp only [c4, c5, if_false]
      exact sqrt_clamp_Z (Z_mul_left he hp) he hdt

/-- **`sqrt_controller_accel` with a zero command** returns `0.0`: `rate_cmd * rate_state` is a
zero, so `is_positive` of it is false (`control.cpp:676-678`). -/
theorem sqrt_controller_accel_Z {error rate_cmd rate_state p sol : Float32} (hc : Z rate_cmd)
    (hs : rate_state.IsFinite) : sqrt_controller_accel error rate_cmd rate_state p sol = 0.0 := by
  unfold sqrt_controller_accel
  rw [is_positive_Z (Z_mul_left hc hs)]
  rfl

/-! ## The shaping functions -/

/-- **`shape_accel` with a zero target and a zero state** returns a zero, for finite
`|jerk_max|, |dt| ≤ 10¹⁸`. -/
theorem shape_accel_Z {ad a j dt : Float32} (had : Z ad) (ha : Z a) (hj : j.IsFinite)
    (hdt : dt.IsFinite) (hjb : |j.toReal| ≤ 1e18) (hdtb : |dt.toReal| ≤ 1e18) :
    Z (shape_accel ad a j dt) := by
  unfold shape_accel
  split_ifs with h1 h2
  · exact ha
  · have hj0 := is_positive_ge hj (by simpa using h1)
    have hd0 := is_positive_ge hdt h2
    have hb : |j.toReal * dt.toReal| ≤ 1e38 := by
      rw [abs_mul]; nlinarith [abs_nonneg j.toReal, abs_nonneg dt.toReal]
    have hb' : |(-j).toReal * dt.toReal| ≤ 1e38 := by rwa [Float32.toReal_neg, neg_mul, abs_neg]
    have hjn := (Float32.isFinite_neg j).2 hj
    have he := eps_pos
    exact Z_add ha (constrain_Z (Z_sub had ha) (fin_mul hjn hdt hb') (fin_mul hj hdt hb)
      (nonpos_mul hjn hdt hb' (by rw [Float32.toReal_neg]; nlinarith))
      (nonneg_mul hj hdt hb (by nlinarith)))
  · exact ha

/-- **`shape_pos_vel_accel` at zero error and zero state.** If the position error
`tofloat(pos_desired - pos)` is a zero and the velocities and accelerations (desired and state) are
zeros, the returned acceleration is a zero; parameters finite with `|jerk_max| ≤ 10¹¹`,
`|accel_max|, |dt| ≤ 10¹⁸`. -/
theorem shape_pos_vel_accel_Z {pos_desired pos : postype}
    {vel_desired accel_desired vel accel vel_min vel_max accel_min accel_max jerk_max dt : Float32}
    (hpe : Z (tofloat (pos_desired - pos))) (hvd : Z vel_desired) (had : Z accel_desired)
    (hv : Z vel) (ha : Z accel) (hvmin : vel_min.IsFinite) (hvmax : vel_max.IsFinite)
    (hamin : accel_min.IsFinite) (hamax : accel_max.IsFinite) (hj : jerk_max.IsFinite)
    (hdt : dt.IsFinite) (hjb : |jerk_max.toReal| ≤ 1e11) (hamb : |accel_max.toReal| ≤ 1e18)
    (hdtb : |dt.toReal| ≤ 1e18) (limit_total : Bool) :
    Z (shape_pos_vel_accel pos_desired vel_desired accel_desired pos vel accel vel_min vel_max
      accel_min accel_max jerk_max dt limit_total) := by
  unfold shape_pos_vel_accel
  simp only [is_positive_Z hpe, Bool.false_eq_true, if_false]
  split
  · exact ha
  · rename_i hg
    simp only [Bool.or_eq_true, Bool.not_eq_true', not_or] at hg
    obtain ⟨⟨⟨⟨-, -⟩, hamin_neg⟩, hamax_pos⟩, hj_pos⟩ := hg
    have he := eps_pos
    have hj0 := is_positive_ge hj (by simpa using hj_pos)
    have ham0 := is_positive_ge hamax (by simpa using hamax_pos)
    have hamn := is_negative_le hamin (by simpa using hamin_neg)
    rw [eps_eq] at hj0 ham0 hamn
    have hampos : 0 < accel_max.toReal := by linarith
    -- the gain `k_v = jerk_max / accel_max`
    have hkx : |jerk_max.toReal / accel_max.toReal| ≤ 1e18 := by
      rw [abs_div, abs_of_pos hampos, div_le_iff₀ hampos]; nlinarith
    obtain ⟨hkf, hkb, hklo⟩ := div_abs_le hj hamax hampos.ne' (hkx.trans (by norm_num))
    have hkpos : 0 < (jerk_max / accel_max).toReal := by
      have h1 : 1e-26 ≤ jerk_max.toReal / accel_max.toReal := by
        rw [le_div_iff₀ hampos]; have := (abs_le.1 hamb).2; nlinarith
      have := hklo (by linarith)
      linarith
    have hv1 : Z (sqrt_controller (tofloat (pos_desired - pos)) (jerk_max / accel_max) accel_max dt) :=
      sqrt_controller_Z hpe hkf hamax hdt (by linarith) hamb
    have hvc : (vel - vel_desired).IsFinite := (Z_sub hv hvd).1
    rw [sqrt_controller_accel_Z hv1 hvc]
    have hv2 : Z (sqrt_controller (tofloat (pos_desired - pos)) (jerk_max / accel_max) accel_max dt +
        0.0 / (jerk_max / accel_max)) := Z_add hv1 (Z_div Z_lit0 hkf hkpos.ne')
    generalize sqrt_controller (tofloat (pos_desired - pos)) (jerk_max / accel_max) accel_max dt +
        0.0 / (jerk_max / accel_max) = v2 at hv2 ⊢
    have hv3 : Z (if is_positive vel_max = true then
        MIN (if is_negative vel_min = true then MAX v2 vel_min else v2) vel_max
        else if is_negative vel_min = true then MAX v2 vel_min else v2) := by
      split_ifs with h1 h2 h2
      · rw [MAX_Z_left hv2 hvmin h2, MIN_Z_left hv2 hvmax h1]; exact hv2
      · rw [MIN_Z_left hv2 hvmax h1]; exact hv2
      · rw [MAX_Z_left hv2 hvmin h2]; exact hv2
      · exact hv2
    generalize (if is_positive vel_max = true then
        MIN (if is_negative vel_min = true then MAX v2 vel_min else v2) vel_max
        else if is_negative vel_min = true then MAX v2 vel_min else v2) = v3 at hv3 ⊢
    have hv4 := Z_add hvd hv3
    generalize vel_desired + v3 = v4 at hv4 ⊢
    have hv5 : Z (if limit_total = true then
        (if is_positive vel_max = true then
          MIN (if is_negative vel_min = true then MAX v4 vel_min else v4) vel_max
          else if is_negative vel_min = true then MAX v4 vel_min else v4) else v4) := by
      split_ifs with h0 h1 h2 h2
      · rw [MAX_Z_left hv4 hvmin h2, MIN_Z_left hv4 hvmax h1]; exact hv4
      · rw [MIN_Z_left hv4 hvmax h1]; exact hv4
      · rw [MAX_Z_left hv4 hvmin h2]; exact hv4
      · exact hv4
      · exact hv4
    generalize (if limit_total = true then
        (if is_positive vel_max = true then
          MIN (if is_negative vel_min = true then MAX v4 vel_min else v4) vel_max
          else if is_negative vel_min = true then MAX v4 vel_min else v4) else v4) = v5 at hv5 ⊢
    have hc1 : Z (constrain_float ((v5 - vel) * (jerk_max / accel_max)) accel_min accel_max) :=
      constrain_Z (Z_mul_left (Z_sub hv5 hv) hkf) hamin hamax (by linarith) hampos.le
    have hc2 := Z_add hc1 had
    have hc3 : Z (if limit_total = true then constrain_float
        (constrain_float ((v5 - vel) * (jerk_max / accel_max)) accel_min accel_max + accel_desired)
        accel_min accel_max
        else constrain_float ((v5 - vel) * (jerk_max / accel_max)) accel_min accel_max +
          accel_desired) := by
      split
      · exact constrain_Z hc2 hamin hamax (by linarith) hampos.le
      · exact hc2
    exact shape_accel_Z hc3 ha hj hdt (by linarith) hdtb

/-- **`shape_angle_vel_accel` at zero error and zero state** (the angles are widened to `double`
and the difference narrowed back, hence `ConvZero`). Parameters finite with
`|angle_jerk_max| ≤ 10¹¹`, `|angle_accel_max|, |dt| ≤ 10¹⁸`. -/
theorem shape_angle_vel_accel_Z (C : ConvZero)
    {angle_desired angle_vel_desired angle_accel_desired angle angle_vel angle_accel angle_vel_min
      angle_vel_max angle_accel_max angle_jerk_max dt : Float32}
    (had : Z angle_desired) (havd : Z angle_vel_desired) (haad : Z angle_accel_desired)
    (ha : Z angle) (hav : Z angle_vel) (haa : Z angle_accel) (hvmin : angle_vel_min.IsFinite)
    (hvmax : angle_vel_max.IsFinite) (hamax : angle_accel_max.IsFinite)
    (hj : angle_jerk_max.IsFinite) (hdt : dt.IsFinite) (hjb : |angle_jerk_max.toReal| ≤ 1e11)
    (hamb : |angle_accel_max.toReal| ≤ 1e18) (hdtb : |dt.toReal| ≤ 1e18) (limit_total : Bool) :
    Z (shape_angle_vel_accel angle_desired angle_vel_desired angle_accel_desired angle angle_vel
      angle_accel angle_vel_min angle_vel_max angle_accel_max angle_jerk_max dt limit_total) := by
  unfold shape_angle_vel_accel
  simp only []
  rw [wrap_PI_Z (Z_sub had ha)]
  have h1 : ZD (topostype (angle + (angle_desired - angle))) :=
    C.toFloat_zero _ (Z_add ha (Z_sub had ha))
  have h2 : ZD (topostype angle) := C.toFloat_zero _ ha
  have hpe : Z (tofloat (topostype (angle + (angle_desired - angle)) - topostype angle)) :=
    C.toFloat32_zero _ (ZD_sub h1 h2)
  exact shape_pos_vel_accel_Z hpe havd haad hav haa hvmin hvmax ((Float32.isFinite_neg _).2 hamax)
    hamax hj hdt hjb hamb hdtb limit_total

theorem radians1800_spec : (radians 1800).IsFinite ∧ 31 < (radians 1800).toReal ∧
    (radians 1800).toReal < 32 := by
  obtain ⟨h1, h2⟩ := litPos (x := radians 1800) (m := 16470993) (e := -19) (hm := by decide)
    (by rfl)
  refine ⟨h1, ?_, ?_⟩ <;> rw [h2] <;> norm_num

/-- **`attitude_command_model` at zero error, zero desired rate and zero shaping state** returns the
zero pair `(target_ang_vel, target_ang_accel)`, for finite parameters with `|accel_max| ≤ 1000`,
`|dt| ≤ 10¹⁸`. -/
theorem attitude_command_model_Z (C : ConvZero)
    {error_angle desired_ang_vel target_ang_vel target_ang_accel max_ang_vel accel_max input_tc
      dt : Float32}
    (he : Z error_angle) (hd : Z desired_ang_vel) (hv : Z target_ang_vel) (ha : Z target_ang_accel)
    (hmax : max_ang_vel.IsFinite) (hacc : accel_max.IsFinite) (htc : input_tc.IsFinite)
    (hdt : dt.IsFinite) (haccb : |accel_max.toReal| ≤ 1000) (hdtb : |dt.toReal| ≤ 1e18) :
    Z (AC_AttitudeControl.attitude_command_model error_angle desired_ang_vel target_ang_vel
        target_ang_accel max_ang_vel accel_max input_tc dt).1 ∧
      Z (AC_AttitudeControl.attitude_command_model error_angle desired_ang_vel target_ang_vel
        target_ang_accel max_ang_vel accel_max input_tc dt).2 := by
  unfold AC_AttitudeControl.attitude_command_model
  split
  · exact ⟨hv, ha⟩
  · rename_i hdp
    have hdt0 := is_positive_ge hdt (by simpa using hdp)
    have he' := eps_pos
    rw [eps_eq] at hdt0
    -- the acceleration limit, in `(0, 1000]`
    have hA : (if (!is_positive accel_max) = true then radians 1800 else accel_max).IsFinite ∧
        |(if (!is_positive accel_max) = true then radians 1800 else accel_max).toReal| ≤ 1000 := by
      split
      · obtain ⟨h1, h2, h3⟩ := radians1800_spec
        exact ⟨h1, by rw [abs_le]; constructor <;> linarith⟩
      · exact ⟨hacc, haccb⟩
    -- the time constant, at least `2⁻²³`
    have hT : (if (!is_positive input_tc) = true then dt * 10.0 else input_tc).IsFinite ∧
        1 / 8388608 ≤ (if (!is_positive input_tc) = true then dt * 10.0 else input_tc).toReal := by
      split
      · have hb : |dt.toReal * (10.0 : Float32).toReal| ≤ 1e38 := by
          rw [lit_ten.2, abs_mul]; norm_num; linarith
        have hge := ge_mul hdt lit_ten.1 hdt hb (by rw [lit_ten.2]; nlinarith)
        exact ⟨fin_mul hdt lit_ten.1 hb, by linarith⟩
      · rename_i hp
        have := is_positive_ge htc (by simpa using hp)
        rw [eps_eq] at this
        exact ⟨htc, this⟩
    generalize (if (!is_positive accel_max) = true then radians 1800 else accel_max) = A at hA ⊢
    generalize (if (!is_positive input_tc) = true then dt * 10.0 else input_tc) = T at hT ⊢
    obtain ⟨hAf, hAb⟩ := hA
    obtain ⟨hTf, hT0⟩ := hT
    have hTpos : 0 < T.toReal := by linarith
    have hjx : |A.toReal / T.toReal| ≤ 1e10 := by
      rw [abs_div, abs_of_pos hTpos, div_le_iff₀ hTpos]; nlinarith [abs_nonneg A.toReal]
    obtain ⟨hjf, hjb, -⟩ := div_abs_le hAf hTf hTpos.ne' (hjx.trans (by norm_num))
    have hacc' := shape_angle_vel_accel_Z C he hd Z_lit0 Z_lit0 hv ha
      ((Float32.isFinite_neg _).2 hmax) hmax hAf hjf hdt (by linarith)
      (hAb.trans (by norm_num)) hdtb true
    exact ⟨Z_add hv (Z_mul_left hacc' hdt), hacc'⟩

/-! ## Quaternions -/

theorem hmul_q (q v : Quaternion) : q * v = Quaternion.mul q v := rfl
theorem hmul_qv (q : Quaternion) (v : Vector3f) : q * v = Quaternion.mul_vec q v := rfl

theorem IdQ_lit : IdQ ⟨1.0, 0.0, 0.0, 0.0⟩ := ⟨lit_one, Z_lit0, Z_lit0, Z_lit0⟩

/-- `from_axis_angle(axis, θ)` at a zero angle is the identity literal (the `is_zero(theta)`
branch, `quaternion.cpp:470-473`). -/
theorem from_axis_angle_theta_Z (axis : Vector3f) {θ : Float32} (h : Z θ) :
    Quaternion.from_axis_angle_theta axis θ = ⟨1.0, 0.0, 0.0, 0.0⟩ := by
  unfold Quaternion.from_axis_angle_theta; rw [is_zero_Z h]; rfl

/-- `from_axis_angle(v)` at the zero vector is the identity literal (`quaternion.cpp:456-459`). -/
theorem from_axis_angle_Z {v : Vector3f} (h : ZV v) :
    Quaternion.from_axis_angle v = ⟨1.0, 0.0, 0.0, 0.0⟩ := by
  unfold Quaternion.from_axis_angle; simp only []; rw [is_zero_Z (ZV_length h)]; rfl

/-- `to_axis_angle` of the identity is the zero vector (`l = sqrt(0)` is zero, the `is_zero`
branch returns `(q2, q3, q4)`). -/
theorem to_axis_angle_Id {q : Quaternion} (h : IdQ q) : ZV q.to_axis_angle := by
  obtain ⟨-, h2, h3, h4⟩ := h
  unfold Quaternion.to_axis_angle; simp only []
  rw [is_zero_Z (Z_sqrt (Z_add (Z_add (Z_sq h2) (Z_sq h3)) (Z_sq h4)))]
  exact ⟨h2, h3, h4⟩

/-- The Hamilton product of two identities is the identity. -/
theorem mul_Id {q v : Quaternion} (hq : IdQ q) (hv : IdQ v) : IdQ (q * v) := by
  obtain ⟨a1, a2, a3, a4⟩ := hq
  obtain ⟨b1, b2, b3, b4⟩ := hv
  rw [hmul_q]; unfold Quaternion.mul; simp only []
  refine ⟨One_sub_Z (One_sub_Z (One_sub_Z (One_mul a1 b1) (Z_mul_left a2 b2.1))
      (Z_mul_left a3 b3.1)) (Z_mul_left a4 b4.1), ?_, ?_, ?_⟩
  · exact Z_sub (Z_add (Z_add (Z_mul_right a1.1 b2) (Z_mul_left a2 b1.1)) (Z_mul_left a3 b4.1))
      (Z_mul_left a4 b3.1)
  · exact Z_add (Z_add (Z_sub (Z_mul_right a1.1 b3) (Z_mul_left a2 b4.1)) (Z_mul_left a3 b1.1))
      (Z_mul_left a4 b2.1)
  · exact Z_add (Z_sub (Z_add (Z_mul_right a1.1 b4) (Z_mul_left a2 b3.1)) (Z_mul_left a3 b2.1))
      (Z_mul_left a4 b1.1)

theorem inverse_Id {q : Quaternion} (h : IdQ q) : IdQ q.inverse :=
  ⟨h.1, Z_neg h.2.1, Z_neg h.2.2.1, Z_neg h.2.2.2⟩

/-- `normalize` of the identity is the identity (`length = sqrt(1) = 1`, not `is_zero`). -/
theorem normalize_Id {q : Quaternion} (h : IdQ q) : IdQ q.normalize := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hl : One q.length :=
    One_sqrt (One_add_Z (One_add_Z (One_add_Z (One_mul h1 h1) (Z_mul_left h2 h2.1))
      (Z_mul_left h3 h3.1)) (Z_mul_left h4 h4.1))
  unfold Quaternion.normalize; simp only []
  rw [is_zero_One hl]
  have hinv : One (1.0 / q.length) := One_div lit_one hl
  exact ⟨One_mul h1 hinv, Z_mul_left h2 hinv.1, Z_mul_left h3 hinv.1, Z_mul_left h4 hinv.1⟩

/-- Two vectors with finite components of equal values. -/
def SameV (a b : Vector3f) : Prop :=
  (a.x.IsFinite ∧ a.x.toReal = b.x.toReal) ∧ (a.y.IsFinite ∧ a.y.toReal = b.y.toReal) ∧
    (a.z.IsFinite ∧ a.z.toReal = b.z.toReal)

/-- Rotating a finite vector by the identity gives it back exactly (in value). -/
theorem mul_vec_Id {q : Quaternion} (hq : IdQ q) {v : Vector3f} (hv : FinV v) : SameV (q * v) v := by
  obtain ⟨h1, h2, h3, h4⟩ := hq
  obtain ⟨vx, vy, vz⟩ := hv
  rw [hmul_qv]; unfold Quaternion.mul_vec; simp only []
  have u0 : Z (q.q3 * v.z - q.q4 * v.y) := Z_sub (Z_mul_left h3 vz) (Z_mul_left h4 vy)
  have u1 : Z (q.q4 * v.x - q.q2 * v.z) := Z_sub (Z_mul_left h4 vx) (Z_mul_left h2 vz)
  have u2 : Z (q.q2 * v.y - q.q3 * v.x) := Z_sub (Z_mul_left h2 vy) (Z_mul_left h3 vx)
  have d0 := Z_add u0 u0
  have d1 := Z_add u1 u1
  have d2 := Z_add u2 u2
  refine ⟨add_Z_right vx (Z_sub (Z_add (Z_mul_right h1.1 d0) (Z_mul_left h3 d2.1))
      (Z_mul_left h4 d1.1)), add_Z_right vy (Z_sub (Z_add (Z_mul_right h1.1 d1)
      (Z_mul_left h4 d0.1)) (Z_mul_left h2 d2.1)), add_Z_right vz (Z_sub (Z_add
      (Z_mul_right h1.1 d2) (Z_mul_left h2 d1.1)) (Z_mul_left h3 d0.1))⟩

theorem ZV_of_SameV {a b : Vector3f} (h : SameV a b) (hb : ZV b) : ZV a :=
  ⟨Z_of_eq h.1 hb.1, Z_of_eq h.2.1 hb.2.1, Z_of_eq h.2.2 hb.2.2⟩

theorem ZV.fin {v : Vector3f} (h : ZV v) : FinV v := ⟨h.1.1, h.2.1.1, h.2.2.1⟩

end Contracts.CopterZero
