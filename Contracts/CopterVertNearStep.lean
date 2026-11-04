import Contracts.CopterVertNear
import Contracts.CopterCode

/-!
# The vertical path at a hover sample, function by function

Each lemma takes one function of the vertical path of the ported ArduCopter stack, with its
relevant inputs `Near32` (or `Near64`) the real values of `Contracts.CopterVert` and its other
inputs at the hover (zeros, ones, the configuration), and concludes that the outputs are `Near32`
the corresponding line of `CopterVert.stepN`, with explicit bounds.
-/

open Float.Model UnpackedFloat AP_Math Contracts.CopterVert

namespace Contracts.CopterVertNear

noncomputable section

attribute [local irreducible] av aa am kp ki kv kpos dtc g k CopterVert.h Gf Hf

/-! ## The position P controller `AC_P_1D.update_all` (`PSC_D_POS_P = 1`) -/

/-- **Position loop.** With the target at `-1` exactly, the position estimate within `10⁻¹⁵` of
`ζ - 1` (binary64), and the error limits and `D1_max` at least `1 cm` away, the error is narrowed to
`float` within `3.1 · 10⁻¹⁰` of `-ζ`, no clamp applies, `sqrt_controller` is in its linear branch
(`|err| ≤ D1_max / P²`) and returns `err · 1 = err`: the velocity target is within `3.1 · 10⁻¹⁰` of
`-kpos ζ`. The target is returned unchanged. -/
theorem p1d_near (hN : NarrowSpec 1) (s : AC_P_1D.State) {tgt meas : Float} {ζ δ : ℝ}
    (htgt : Near64 tgt (-1) 0) (hmeas : Near64 meas (ζ - 1) δ) (hδ : δ ≤ 1e-15)
    (hζ : |ζ| ≤ 1 / 200)
    (hmin : s._error_min.IsFinite) (hmin' : s._error_min.toReal ≤ -(1 / 100))
    (hmax : s._error_max.IsFinite) (hmax' : 1 / 100 ≤ s._error_max.toReal)
    (hD1 : s._D1_max.IsFinite) (hD1' : 1 / 100 ≤ s._D1_max.toReal) :
    Near32 (AC_P_1D.update_all ⟨AC_PosControl.POSCONTROL_D_POS_P⟩ s tgt meas).2.2
        (-(kpos * ζ)) 3.1e-10 ∧
      (AC_P_1D.update_all ⟨AC_PosControl.POSCONTROL_D_POS_P⟩ s tgt meas).2.1 = tgt ∧
      Near32 (AC_P_1D.update_all ⟨AC_PosControl.POSCONTROL_D_POS_P⟩ s tgt meas).1._error
        (-ζ) 3.1e-10 := by
  have hu := u32_le; have hu0 := u32_nonneg; have hη := η32_le; have hη0 := η32_nonneg
  have hζ' := abs_le.1 hζ
  have hδ0 : 0 ≤ δ := (abs_nonneg _).trans hmeas.2
  -- binary64 difference and narrowing
  have e1 : Near64 (tgt - meas) (-ζ) 1.1e-15 := by
    have := near64_sub htgt hmeas (B := 0.0051) (bnd3 (by linarith) (by linarith)) (by norm_num)
    refine ⟨this.1, ?_⟩
    have h2 := this.2
    rw [show (-1 : ℝ) - (ζ - 1) = -ζ by ring] at h2
    refine h2.trans ?_
    have : (2 : ℝ) ^ (-53 : ℤ) * 0.0051 ≤ 1e-18 := by norm_num
    linarith
  have e2 : Near32 (tofloat (tgt - meas)) (-ζ) 3.1e-10 := by
    have := near_narrow hN e1 (by have := abs_neg ζ ▸ hζ; linarith)
    refine this.mono ?_
    have : u32 * (|-ζ| + 1.1e-15) ≤ 5.97e-8 * (1 / 200 + 1.1e-15) := by
      rw [abs_neg]; gcongr
    linarith
  set err := tofloat (tgt - meas) with herr
  have hlo := e2.lo; have hhi := e2.hi
  -- no clamp
  have c1 : (is_negative s._error_min && decide (err < s._error_min)) = false := by
    have : ¬ err < s._error_min := not_lt_of e2.1 hmin (by linarith)
    simp [this]
  have c2 : (is_positive s._error_max && decide (err > s._error_max)) = false := by
    have : ¬ err > s._error_max := not_lt_of hmax e2.1 (by linarith)
    simp [this]
  -- the linear branch of `sqrt_controller`
  have one_p := one_D_POS_P
  have hsq : One (AP_Math.sq AC_PosControl.POSCONTROL_D_POS_P) := by
    have := mul_one_val one_p.1 one_p
    exact ⟨this.1, by rw [AP_Math.sq, this.2, one_p.2]⟩
  have hld := div_exact hD1 hsq.1 (by rw [hsq.2]; norm_num) hD1 (by rw [hsq.2, div_one])
  have hsc : sqrt_controller err AC_PosControl.POSCONTROL_D_POS_P s._D1_max 0.0 =
      err * AC_PosControl.POSCONTROL_D_POS_P := by
    unfold sqrt_controller
    have b1 : (is_negative s._D1_max || is_zero s._D1_max) = false := by
      rw [is_negative_false hD1 (by linarith), is_zero_false hD1 (by
        rw [abs_of_pos (by linarith)]; linarith)]; rfl
    have b2 : is_zero AC_PosControl.POSCONTROL_D_POS_P = false :=
      is_zero_false one_p.1 (by rw [one_p.2]; norm_num)
    have b3 : ¬ err > s._D1_max / AP_Math.sq AC_PosControl.POSCONTROL_D_POS_P :=
      not_lt_of hld.1 e2.1 (by rw [hld.2]; linarith)
    have hnld := (Float32.isFinite_neg (s._D1_max / AP_Math.sq AC_PosControl.POSCONTROL_D_POS_P)).2 hld.1
    have b4 : ¬ err < -(s._D1_max / AP_Math.sq AC_PosControl.POSCONTROL_D_POS_P) :=
      not_lt_of e2.1 hnld (by rw [Float32.toReal_neg, hld.2]; linarith)
    have b5 : is_positive (0.0 : Float32) = false := by decide
    simp only [b1, b2, b5, Bool.false_eq_true, if_false]
    show (if err > s._D1_max / AP_Math.sq AC_PosControl.POSCONTROL_D_POS_P then _ else
      if err < -(s._D1_max / AP_Math.sq AC_PosControl.POSCONTROL_D_POS_P) then _ else _) = _
    rw [if_neg b3, if_neg b4]
  have hout : Near32 (err * AC_PosControl.POSCONTROL_D_POS_P) (-(kpos * ζ)) 3.1e-10 :=
    (e2.mul_one one_p).congr (by rw [kpos, one_mul])
  simp only [AC_P_1D.update_all, ← herr, c1, c2, Bool.false_eq_true, if_false, Id.run, hsc]
  exact ⟨hout, rfl, e2⟩

/-! ## The velocity PID `AC_PID_Basic.update_all` (`P = 5`, `I = D = FF = 0`, 5 Hz error filter) -/

/-- The velocity PID's gains: the code defaults of `PSC_D_VEL_*` (`AC_PosControl.cpp:360`). -/
def pv : AC_PID_Basic.Params := AC_PosControl.defaults._pid_vel_d_m

theorem pv_P : pv.P = AC_PosControl.POSCONTROL_D_VEL_P := rfl
theorem pv_I : is_zero pv.I = true := by decide
theorem Z_pv_D : Z pv.D := Z_lit0
theorem Z_pv_FF : Z pv.FF := Z_lit0
theorem pv_alphaE : AC_PID_Basic.get_filt_E_alpha pv dtF =
    calc_lowpass_alpha_dt dtF AC_PosControl.POSCONTROL_D_VEL_FILT_HZ := rfl
theorem pos_dtF : is_positive dtF = true := by decide

/-- `calc_lowpass_alpha_dt(dt, PSC_D_VEL_FLTD = 5)`, the velocity derivative filter: `alpha_v`. -/
theorem near_avD : Near32 (AC_PID_Basic.get_filt_D_alpha pv dtF) av 0 := by
  have h : (AC_PID_Basic.get_filt_D_alpha pv dtF).toModel.unpack =
      .finite .positive 9773802 (-27) (by decide) := by rfl
  obtain ⟨h1, h2⟩ := lit32 _ _ _ h
  exact Near32.of_val h1 (by rw [h2, av]; norm_num)

/-- The velocity PID outside reset, written out: the error filter, the derivative filter, the
integrator set to `0` by `update_i` (`I = 0`), and the output `P_out + I + D_out + FF_out`. -/
theorem pidv_eval (s : AC_PID_Basic.State) {tgt meas : Float32} (ht : tgt.IsFinite)
    (hm : meas.IsFinite) (hr : s._reset_filter = false) (ln lp : Bool) :
    (AC_PID_Basic.update_all pv s tgt meas dtF ln lp).1._error =
      s._error + AC_PID_Basic.get_filt_E_alpha pv dtF * ((tgt - meas) - s._error) ∧
    (AC_PID_Basic.update_all pv s tgt meas dtF ln lp).1._integrator = 0.0 ∧
    (AC_PID_Basic.update_all pv s tgt meas dtF ln lp).1._reset_filter = false ∧
    (AC_PID_Basic.update_all pv s tgt meas dtF ln lp).1._derivative =
      s._derivative + AC_PID_Basic.get_filt_D_alpha pv dtF *
        (((s._error + AC_PID_Basic.get_filt_E_alpha pv dtF * ((tgt - meas) - s._error)) - s._error)
          / dtF - s._derivative) ∧
    (AC_PID_Basic.update_all pv s tgt meas dtF ln lp).2 =
      (s._error + AC_PID_Basic.get_filt_E_alpha pv dtF * ((tgt - meas) - s._error)) * pv.P + 0.0 +
      (s._derivative + AC_PID_Basic.get_filt_D_alpha pv dtF *
        (((s._error + AC_PID_Basic.get_filt_E_alpha pv dtF * ((tgt - meas) - s._error)) - s._error)
          / dtF - s._derivative)) * pv.D + tgt * pv.FF := by
  simp only [AC_PID_Basic.update_all, AC_PID_Basic.update_i, isFinite_true ht, isFinite_true hm,
    not_isNaN ht, not_isNaN hm, hr, pos_dtF, pv_I]
  simp

/-- **Velocity loop.** Outside reset, with the stored error filter `E` within the box
(`|E| ≤ 1/20`), the stored derivative filter finite with `|D| ≤ 3`, the velocity target within
`3.1 · 10⁻¹⁰` of `-kpos ζ` and the velocity reading within `6 · 10⁻¹⁰` of `w`: the new error filter
is within `3.6 · 10⁻⁹` of `(1 - av) E + av (-kpos ζ - w)` (the `Ev'` line of `stepN`, so
`|n1| ≤ 3.6 · 10⁻⁹`), the integrator is `0`, the derivative filter stays finite with `|D'| ≤ 3`
(it does not reach the output, `D = 0`), and the output is within `1.5 · 10⁻⁸` of `kv E'` with `E'`
the exact value of the new error filter. -/
theorem pidv_near (s : AC_PID_Basic.State) {tgt meas : Float32} {ζ w : ℝ}
    (hr : s._reset_filter = false) (hE : s._error.IsFinite) (hEb : |s._error.toReal| ≤ 1 / 20)
    (hD : s._derivative.IsFinite) (hDb : |s._derivative.toReal| ≤ 3)
    (ht : Near32 tgt (-(kpos * ζ)) 3.1e-10) (hm : Near32 meas w 6e-10)
    (hζ : |ζ| ≤ 1 / 200) (hw : |w| ≤ 1 / 100) (ln lp : Bool) :
    Near32 (AC_PID_Basic.update_all pv s tgt meas dtF ln lp).1._error
        ((1 - av) * s._error.toReal + av * (-(kpos * ζ) - w)) 3.6e-9 ∧
      Z (AC_PID_Basic.update_all pv s tgt meas dtF ln lp).1._integrator ∧
      (AC_PID_Basic.update_all pv s tgt meas dtF ln lp).1._reset_filter = false ∧
      (AC_PID_Basic.update_all pv s tgt meas dtF ln lp).1._derivative.IsFinite ∧
      |(AC_PID_Basic.update_all pv s tgt meas dtF ln lp).1._derivative.toReal| ≤ 3 ∧
      Near32 (AC_PID_Basic.update_all pv s tgt meas dtF ln lp).2
        (kv * (AC_PID_Basic.update_all pv s tgt meas dtF ln lp).1._error.toReal) 1.5e-8 := by
  obtain ⟨q1, q2, q3, q4, q5⟩ := pidv_eval s ht.1 hm.1 hr ln lp
  rw [q1, q2, q3, q4, q5]
  have hu := u32_le; have hu0 := u32_nonneg; have hη := η32_le; have hη0 := η32_nonneg
  have hζ' := abs_le.1 hζ; have hw' := abs_le.1 hw; have hEb' := abs_le.1 hEb
  have hDb' := abs_le.1 hDb
  have hav := av_eq
  have hkpos := kpos_eq
  have hE0 := Near32.exact hE
  -- the error filter
  have d1 : Near32 (tgt - meas) (-(kpos * ζ) - w) 1.82e-9 := by
    have := near_sub ht hm (B := 0.0151) (bnd3 (by rw [hkpos]; linarith) (by rw [hkpos]; linarith))
      (by norm_num)
    exact this.mono (by linarith)
  have d2 : Near32 ((tgt - meas) - s._error) ((-(kpos * ζ) - w) - s._error.toReal) 5.8e-9 := by
    have := near_sub d1 hE0 (B := 0.0651) (bnd3 (by rw [hkpos]; linarith) (by rw [hkpos]; linarith))
      (by norm_num)
    exact this.mono (by linarith)
  have d3 : Near32 (AC_PID_Basic.get_filt_E_alpha pv dtF * ((tgt - meas) - s._error))
      (av * ((-(kpos * ζ) - w) - s._error.toReal)) 7.1e-10 := by
    rw [pv_alphaE]
    have := near_const_mul near_av d2 (Ra := 0.0651) (bnd (by rw [hkpos]; linarith)
      (by rw [hkpos]; linarith)) (by rw [abs_of_pos (show (0 : ℝ) < av by rw [hav]; norm_num), hav]; norm_num)
    refine this.mono ?_
    rw [abs_of_pos (show (0 : ℝ) < av by rw [hav]; norm_num), hav]
    nlinarith
  have hE1 : Near32 (s._error + AC_PID_Basic.get_filt_E_alpha pv dtF * ((tgt - meas) - s._error))
      ((1 - av) * s._error.toReal + av * (-(kpos * ζ) - w)) 3.6e-9 := by
    have hr0 : |s._error.toReal + av * ((-(kpos * ζ) - w) - s._error.toReal)| + 0 + 7.1e-10 ≤
        0.0476 := by
      rw [hav, hkpos]
      apply bnd3 <;> nlinarith
    have := near_add hE0 d3 hr0 (by norm_num)
    exact (this.congr (by ring)).mono (by linarith)
  set E' := s._error + AC_PID_Basic.get_filt_E_alpha pv dtF * ((tgt - meas) - s._error) with hE'
  have hE'b : |E'.toReal| ≤ 0.0476 := by
    have := hE1.bound
    have : |(1 - av) * s._error.toReal + av * (-(kpos * ζ) - w)| ≤ 0.04755 := by
      rw [hav, hkpos]; apply bnd <;> nlinarith
    linarith
  -- the derivative filter (computed, not fed back)
  have g1 : Near32 (E' - s._error) (av * ((-(kpos * ζ) - w) - s._error.toReal)) 3.9e-9 := by
    have := near_sub hE1 hE0 (B := 0.00475)
      (bnd3 (by rw [hav, hkpos]; nlinarith) (by rw [hav, hkpos]; nlinarith)) (by norm_num)
    exact (this.congr (by ring)).mono (by linarith)
  have hdtc := dtc_eq
  have g2 : Near32 ((E' - s._error) / dtF) (av * ((-(kpos * ζ) - w) - s._error.toReal) / dtc)
      1.7e-6 := by
    have := near_div g1 near_dtF (Ra := 0.00474) (bnd (by rw [hav, hkpos]; nlinarith)
      (by rw [hav, hkpos]; nlinarith)) (by rw [hdtc]; norm_num) (by rw [hdtc]; norm_num)
    refine this.mono ?_
    rw [hdtc]; norm_num; nlinarith
  have hq : |av * ((-(kpos * ζ) - w) - s._error.toReal) / dtc| ≤ 1.8961 := by
    have hd0 : (0 : ℝ) < dtc := by rw [hdtc]; norm_num
    rw [abs_div, abs_of_pos hd0, div_le_iff₀ hd0, hdtc]
    have : |av * ((-(kpos * ζ) - w) - s._error.toReal)| ≤ 0.00474 := by
      rw [hav, hkpos]; apply bnd <;> nlinarith
    linarith
  have hq' := abs_le.1 hq
  set qr := av * ((-(kpos * ζ) - w) - s._error.toReal) / dtc with hqr
  have g3 : Near32 ((E' - s._error) / dtF - s._derivative)
      (qr - s._derivative.toReal) 2.1e-6 := by
    have := near_sub g2 (Near32.exact hD) (B := 4.8962) (bnd3 (by linarith) (by linarith))
      (by norm_num)
    exact this.mono (by linarith)
  have g4 : Near32 (AC_PID_Basic.get_filt_D_alpha pv dtF * ((E' - s._error) / dtF - s._derivative))
      (av * (qr - s._derivative.toReal)) 1.8e-7 := by
    have := near_const_mul near_avD g3 (Ra := 4.8962) (bnd (by linarith) (by linarith))
      (by rw [abs_of_pos (show (0 : ℝ) < av by rw [hav]; norm_num), hav]; norm_num)
    refine this.mono ?_
    rw [abs_of_pos (show (0 : ℝ) < av by rw [hav]; norm_num), hav]
    nlinarith
  have g5 := near_add (Near32.exact hD) g4 (B := 2.92)
    (bnd3 (by rw [hav]; linarith) (by rw [hav]; linarith)) (by norm_num)
  have hD'b : |(s._derivative + AC_PID_Basic.get_filt_D_alpha pv dtF *
      ((E' - s._error) / dtF - s._derivative)).toReal| ≤ 3 := by
    have := g5.bound
    have : |s._derivative.toReal + av * (qr - s._derivative.toReal)| ≤ 2.9198 := by
      rw [hav]; apply bnd <;> linarith
    linarith
  -- the output
  have o1 : Near32 (E' * pv.P) (E'.toReal * kv) 1.5e-8 := by
    rw [pv_P]
    have := near_mul_const (Near32.exact hE1.1) near_kv (Ra := 0.0476) hE'b
      (by rw [kv_eq]; norm_num)
    refine this.mono ?_
    rw [kv_eq]; norm_num; linarith
  have o2 := (o1.add_zero Z_lit0).add_zero (mul_zero_Z g5.1 Z_pv_D) |>.add_zero (mul_zero_Z ht.1 Z_pv_FF)
  exact ⟨hE1, Z_lit0, rfl, g5.1, hD'b, o2.congr (by ring)⟩

/-! ## The acceleration measurement `get_accel_ef().z + GRAVITY_MSS` -/

/-- **Acceleration measurement.** A reading within `6 · 10⁻⁷` of the plant's specific force
`-k (φ + 4/9)` (the actuator of the last period is `4/9 + φ`), plus `GRAVITY_MSS`, is within
`7.8 · 10⁻⁷` of `-k φ`: the reading error, one rounding (`2⁻²⁴ · 0.23`), and the constant mismatch
`GRAVITY_MSS - 9.80665 = 1.6174 · 10⁻⁷`. -/
theorem accel_meas_near {fs : Float32} {φ : ℝ} (hf : Near32 fs (-(k * (φ + 4 / 9))) 6e-7)
    (hφ : |φ| ≤ 1 / 100) : Near32 (fs + GRAVITY_MSS) (-(k * φ)) 7.8e-7 := by
  have hu := u32_le; have hu0 := u32_nonneg
  have hφ' := abs_le.1 hφ
  have hk := k_eq
  have hG := Gf_eq
  have e1 := near_add hf near_G (B := 0.2217) (bnd3 (by rw [hk, hG]; linarith)
    (by rw [hk, hG]; linarith)) (by norm_num)
  have e2 := e1.shift (r' := -(k * φ)) (d := 1.6175e-7) (by
    rw [show -(k * (φ + 4 / 9)) + Gf - -(k * φ) = Gf - g by rw [hk, hG, g_eq]; ring, G_sub_g]
    norm_num)
  exact e2.mono (by linarith)

/-! ## The acceleration PID `AC_PID.update_all` (`P = 0.05`, `I = 0.1`, `IMAX = 0.8`, 20 Hz) -/

/-- The acceleration PID's gains: the code defaults of `PSC_D_ACC_*` (`AC_PosControl.cpp:361`), with
the RAM `IMAX` at its stored value (the raise to the hover throttle is not taken: `0.4444 < 0.8`). -/
def pa : AC_PID.Params :=
  { P := AC_PosControl.POSCONTROL_D_ACC_P, I := AC_PosControl.POSCONTROL_D_ACC_I,
    D := AC_PosControl.POSCONTROL_D_ACC_D, FF := 0.0, IMAX := AC_PosControl.POSCONTROL_D_ACC_IMAX,
    FLTT := 0.0, FLTE := AC_PosControl.POSCONTROL_D_ACC_FILT_HZ, FLTD := 0.0, SMAX := 0.0,
    PDMX := 0.0, D_FF := 0.0, NTF := 0, NEF := 0 }

/-- The position controller reads exactly these gains while `_pid_accel_d_m_kimax` is at
`PSC_D_ACC_IMAX`. -/
theorem pa_eq (s : AC_PosControl.State)
    (h : s._pid_accel_d_m_kimax = AC_PosControl.POSCONTROL_D_ACC_IMAX) :
    AC_PosControl.pid_accel_d_m_params AC_PosControl.defaults s = pa := by
  simp [AC_PosControl.pid_accel_d_m_params, h, pa, AC_PosControl.defaults]

theorem pa_I : is_zero pa.I = false := by decide
theorem pa_PDMX : is_positive pa.PDMX = false := by decide
theorem pa_alphaT : AC_PID.get_filt_T_alpha pa dtF = 1.0 := alpha0_eq
theorem pa_alphaD : AC_PID.get_filt_D_alpha pa dtF = 1.0 := alpha0_eq
theorem pa_alphaE : AC_PID.get_filt_E_alpha pa dtF =
    calc_lowpass_alpha_dt dtF AC_PosControl.POSCONTROL_D_ACC_FILT_HZ := rfl

/-- New target filter `T + αT (target - T)`. -/
def aT (s : AC_PID.State) (tgt : Float32) : Float32 :=
  s._target + AC_PID.get_filt_T_alpha pa dtF * (tgt - s._target)
/-- New error filter `E + αE ((T' - measurement) - E)`. -/
def aE (s : AC_PID.State) (tgt meas : Float32) : Float32 :=
  s._error + AC_PID.get_filt_E_alpha pa dtF * (aT s tgt - meas - s._error)
/-- New derivative filter. -/
def aD (s : AC_PID.State) (tgt meas : Float32) : Float32 :=
  s._derivative + AC_PID.get_filt_D_alpha pa dtF * ((aE s tgt meas - s._error) / dtF - s._derivative)
/-- New target derivative. -/
def aTD (s : AC_PID.State) (tgt : Float32) : Float32 := (aT s tgt - s._target) / dtF
/-- New integrator. -/
def aI (s : AC_PID.State) (tgt meas : Float32) : Float32 :=
  constrain_float (s._integrator + aE s tgt meas * pa.I * 1.0 * dtF) (-pa.IMAX) pa.IMAX

/-- The acceleration PID outside reset with `limit = false`, written out. -/
theorem pida_eval (s : AC_PID.State) {tgt meas : Float32} (ht : tgt.IsFinite)
    (hm : meas.IsFinite) (hr : s._flags._reset_filter = false) :
    (AC_PID.update_all pa s tgt meas dtF false).1._target = aT s tgt ∧
    (AC_PID.update_all pa s tgt meas dtF false).1._error = aE s tgt meas ∧
    (AC_PID.update_all pa s tgt meas dtF false).1._derivative = aD s tgt meas ∧
    (AC_PID.update_all pa s tgt meas dtF false).1._target_derivative = aTD s tgt ∧
    (AC_PID.update_all pa s tgt meas dtF false).1._integrator = aI s tgt meas ∧
    (AC_PID.update_all pa s tgt meas dtF false).1._flags._reset_filter = false ∧
    (AC_PID.update_all pa s tgt meas dtF false).1._pid_info.FF = aT s tgt * pa.FF ∧
    (AC_PID.update_all pa s tgt meas dtF false).1._pid_info.DFF = aTD s tgt * pa.D_FF ∧
    (AC_PID.update_all pa s tgt meas dtF false).2 =
      aE s tgt meas * pa.P * 1.0 * 1.0 + aD s tgt meas * pa.D * 1.0 * 1.0 + aI s tgt meas := by
  simp only [AC_PID.update_all, AC_PID.update_i, isFinite_true ht, isFinite_true hm, hr, pos_dtF,
    pa_I, pa_PDMX]
  simp [aT, aE, aD, aTD, aI, AC_PID.slew_limiter_modifier_smax_off, hr]

theorem aT_eq (s : AC_PID.State) (tgt : Float32) :
    aT s tgt = s._target + AC_PID.get_filt_T_alpha pa dtF * (tgt - s._target) := rfl
theorem aE_eq (s : AC_PID.State) (tgt meas : Float32) :
    aE s tgt meas = s._error + AC_PID.get_filt_E_alpha pa dtF * (aT s tgt - meas - s._error) := rfl
theorem aD_eq (s : AC_PID.State) (tgt meas : Float32) :
    aD s tgt meas = s._derivative + AC_PID.get_filt_D_alpha pa dtF *
      ((aE s tgt meas - s._error) / dtF - s._derivative) := rfl
theorem aTD_eq (s : AC_PID.State) (tgt : Float32) : aTD s tgt = (aT s tgt - s._target) / dtF := rfl
theorem aI_eq (s : AC_PID.State) (tgt meas : Float32) :
    aI s tgt meas = constrain_float (s._integrator + aE s tgt meas * pa.I * 1.0 * dtF)
      (-pa.IMAX) pa.IMAX := rfl

attribute [irreducible] aT aE aD aTD aI

set_option maxHeartbeats 4000000 in
/-- **Acceleration loop.** Outside reset and with `limit = false`, with the stored target filter
finite and `|T| ≤ 3/10`, the stored error filter `E` finite with `|E| ≤ 13/10`, the integrator `I`
finite with `|I| ≤ 0.00145`, the derivative filter finite with `|D| ≤ 250`, the target within
`1.5 · 10⁻⁸` of `A` (`|A| ≤ 0.2381`; the velocity loop gives `A = kv Ev'`) and the measurement
within `7.8 · 10⁻⁷` of `-k φ`:
* the new error filter is within `3.3 · 10⁻⁷` of `(1 - aa) E + aa (A + k φ)` (the `Ea'` line of
  `stepN`, so `|n2| ≤ 3.3 · 10⁻⁷`);
* the new integrator is within `1.4 · 10⁻¹⁰` of `I + ki dtc E'`, `E'` the exact value of the new
  error filter (the `ι'` line, `|n3| ≤ 1.4 · 10⁻¹⁰`); the clamp to `±IMAX` is inactive;
* the output is within `6.7 · 10⁻⁹` of `kp E' + I'`, `I'` the exact value of the new integrator;
* the target filter (`αT = 1`), the derivative filter (`αD = 1`) and the target derivative stay
  finite and bounded, and the feed-forward terms `FF`, `DFF` are zeros. -/
theorem pida_near (s : AC_PID.State) {tgt meas : Float32} {A φ : ℝ}
    (hr : s._flags._reset_filter = false)
    (hT : s._target.IsFinite) (hTb : |s._target.toReal| ≤ 3 / 10)
    (hE : s._error.IsFinite) (hEb : |s._error.toReal| ≤ 13 / 10)
    (hI : s._integrator.IsFinite) (hIb : |s._integrator.toReal| ≤ 0.00145)
    (hD : s._derivative.IsFinite) (hDb : |s._derivative.toReal| ≤ 250)
    (ht : Near32 tgt A 1.5e-8) (hA : |A| ≤ 0.2381)
    (hm : Near32 meas (-(k * φ)) 7.8e-7) (hφ : |φ| ≤ 1 / 100) :
    Near32 (aE s tgt meas) ((1 - aa) * s._error.toReal + aa * (A + k * φ)) 3.3e-7 ∧
      Near32 (aI s tgt meas) (s._integrator.toReal + ki * dtc * (aE s tgt meas).toReal) 1.4e-10 ∧
      Near32 (AC_PID.update_all pa s tgt meas dtF false).2
        (kp * (aE s tgt meas).toReal + (aI s tgt meas).toReal) 6.7e-9 ∧
      (aT s tgt).IsFinite ∧ |(aT s tgt).toReal| ≤ 3 / 10 ∧
      (aD s tgt meas).IsFinite ∧ |(aD s tgt meas).toReal| ≤ 250 ∧
      Z (aT s tgt * pa.FF) ∧ Z (aTD s tgt * pa.D_FF) := by
  have hu := u32_le; have hu0 := u32_nonneg; have hη := η32_le; have hη0 := η32_nonneg
  have hφ' := abs_le.1 hφ; have hTb' := abs_le.1 hTb; have hEb' := abs_le.1 hEb
  have hIb' := abs_le.1 hIb; have hDb' := abs_le.1 hDb; have hA' := abs_le.1 hA
  have haa := aa_eq
  have hk := k_eq
  have hdtc := dtc_eq
  have hd0 : (0 : ℝ) < dtc := by rw [hdtc]; norm_num
  have hkp := kp_eq
  have hki := ki_eq
  have hT0 := Near32.exact hT; have hE0 := Near32.exact hE
  -- target filter, `αT = 1`
  have t1 : Near32 (tgt - s._target) (A - s._target.toReal) 4.72e-8 := by
    have := near_sub ht hT0 (B := 0.5382) (bnd3 (by linarith) (by linarith)) (by norm_num)
    exact this.mono (by linarith)
  have t2 : Near32 (AC_PID.get_filt_T_alpha pa dtF * (tgt - s._target)) (A - s._target.toReal)
      4.72e-8 := by
    rw [pa_alphaT]; exact Near32.of_eq_val (one_mul_val t1.1 One_lit1).1
      (one_mul_val t1.1 One_lit1).2 t1
  have t3 : Near32 (aT s tgt) A 6.2e-8 := by
    rw [aT_eq]
    have := near_add hT0 t2 (B := 0.2382) (bnd3 (by linarith) (by linarith)) (by norm_num)
    exact (this.congr (by ring)).mono (by linarith)
  have hT'b : |(aT s tgt).toReal| ≤ 3 / 10 := by have := t3.bound; linarith
  -- error filter
  have r1 : Near32 (aT s tgt - meas) (A + k * φ) 8.7e-7 := by
    have := near_sub t3 hm (B := 0.4597) (bnd3 (by rw [hk]; linarith) (by rw [hk]; linarith))
      (by norm_num)
    exact (this.congr (by ring)).mono (by linarith)
  have r2 : Near32 (aT s tgt - meas - s._error) (A + k * φ - s._error.toReal) 9.8e-7 := by
    have := near_sub r1 hE0 (B := 1.7598) (bnd3 (by rw [hk]; linarith) (by rw [hk]; linarith))
      (by norm_num)
    exact this.mono (by linarith)
  have r3 : Near32 (AC_PID.get_filt_E_alpha pa dtF * (aT s tgt - meas - s._error))
      (aa * (A + k * φ - s._error.toReal)) 2.6e-7 := by
    rw [pa_alphaE]
    have := near_const_mul near_aa r2 (Ra := 1.7588) (bnd (by rw [hk]; linarith)
      (by rw [hk]; linarith)) (by rw [abs_of_pos (show (0 : ℝ) < aa by rw [haa]; norm_num), haa]; norm_num)
    refine this.mono ?_
    rw [abs_of_pos (show (0 : ℝ) < aa by rw [haa]; norm_num), haa]
    linarith
  have hE1 : Near32 (aE s tgt meas) ((1 - aa) * s._error.toReal + aa * (A + k * φ)) 3.3e-7 := by
    have hr0 : |s._error.toReal + aa * (A + k * φ - s._error.toReal)| + 0 + 2.6e-7 ≤ 1.1 := by
      rw [haa, hk]; apply bnd3 <;> linarith
    rw [aE_eq]
    have := near_add hE0 r3 hr0 (by norm_num)
    exact (this.congr (by ring)).mono (by linarith)
  have hE'b : |(aE s tgt meas).toReal| ≤ 1.099 := by
    have := hE1.bound
    have : |(1 - aa) * s._error.toReal + aa * (A + k * φ)| ≤ 1.0989 := by
      rw [haa, hk]; apply bnd <;> linarith
    linarith
  have hE'0 := Near32.exact hE1.1
  -- derivative filter, `αD = 1`
  have g1 : Near32 (aE s tgt meas - s._error) (aa * (A + k * φ - s._error.toReal)) 4e-7 := by
    have := near_sub hE1 hE0 (B := 0.4206) (bnd3 (by rw [haa, hk]; linarith)
      (by rw [haa, hk]; linarith)) (by norm_num)
    exact (this.congr (by ring)).mono (by linarith)
  have hgb : |aa * (A + k * φ - s._error.toReal)| ≤ 0.42047 := by
    rw [haa, hk]; apply bnd <;> linarith
  set qr := aa * (A + k * φ - s._error.toReal) / dtc with hqr
  have hq : |qr| ≤ 168.2 := by
    rw [hqr, abs_div, abs_of_pos hd0, div_le_iff₀ hd0, hdtc]; linarith
  have hq' := abs_le.1 hq
  have g2 : Near32 ((aE s tgt meas - s._error) / dtF) qr 1.8e-4 := by
    have := near_div g1 near_dtF (Ra := 0.42047) hgb (by rw [hdtc]; norm_num)
      (by rw [hdtc]; norm_num)
    refine this.mono ?_
    rw [hdtc]; norm_num; linarith
  have g3 : Near32 ((aE s tgt meas - s._error) / dtF - s._derivative) (qr - s._derivative.toReal)
      2.1e-4 := by
    have := near_sub g2 (Near32.exact hD) (B := 418.3) (bnd3 (by linarith) (by linarith))
      (by norm_num)
    exact this.mono (by linarith)
  have g4 : Near32 (AC_PID.get_filt_D_alpha pa dtF * ((aE s tgt meas - s._error) / dtF -
      s._derivative)) (qr - s._derivative.toReal) 2.1e-4 := by
    rw [pa_alphaD]; exact Near32.of_eq_val (one_mul_val g3.1 One_lit1).1
      (one_mul_val g3.1 One_lit1).2 g3
  have g5 : Near32 (aD s tgt meas) qr 2.3e-4 := by
    rw [aD_eq]
    have := near_add (Near32.exact hD) g4 (B := 168.21) (bnd3 (by linarith) (by linarith))
      (by norm_num)
    exact (this.congr (by ring)).mono (by linarith)
  have hD'b : |(aD s tgt meas).toReal| ≤ 250 := by have := g5.bound; linarith
  -- target derivative (finite)
  have td1 : Near32 (aT s tgt - s._target) (A - s._target.toReal) 1.2e-7 := by
    have := near_sub t3 hT0 (B := 0.5383) (bnd3 (by linarith) (by linarith)) (by norm_num)
    exact this.mono (by linarith)
  have td2 := near_div td1 near_dtF (Ra := 0.5381) (bnd (by linarith) (by linarith))
    (by rw [hdtc]; norm_num) (by rw [hdtc]; norm_num)
  -- integrator
  have i1 : Near32 (aE s tgt meas * pa.I) ((aE s tgt meas).toReal * ki) 6.6e-9 := by
    have := near_mul_const hE'0 near_ki (Ra := 1.099) hE'b (by rw [hki]; norm_num)
    refine this.mono ?_
    rw [abs_of_pos (show (0 : ℝ) < ki by rw [hki]; norm_num), hki]; norm_num; linarith
  have i2 := i1.mul_one One_lit1
  have i3 : Near32 (aE s tgt meas * pa.I * 1.0 * dtF) ((aE s tgt meas).toReal * ki * dtc)
      3.3e-11 := by
    have hR : |(aE s tgt meas).toReal * ki| ≤ 0.11 := by
      rw [abs_mul, abs_of_pos (show (0 : ℝ) < ki by rw [hki]; norm_num), hki]; linarith
    have := near_mul_const i2 near_dtF (Ra := 0.11) hR (by rw [abs_of_pos hd0, hdtc]; norm_num)
    refine this.mono ?_
    rw [abs_of_pos hd0, hdtc]; norm_num; linarith
  have hIn : |(aE s tgt meas).toReal * ki * dtc| ≤ 0.000275 := by
    rw [abs_mul, abs_mul, abs_of_pos (show (0 : ℝ) < ki by rw [hki]; norm_num), abs_of_pos hd0,
      hki, hdtc]
    nlinarith [abs_nonneg (aE s tgt meas).toReal]
  have hIn' := abs_le.1 hIn
  have ecomm : (aE s tgt meas).toReal * ki * dtc = ki * dtc * (aE s tgt meas).toReal := by
    rw [mul_assoc, mul_comm]
  have i4 : Near32 (s._integrator + aE s tgt meas * pa.I * 1.0 * dtF)
      (s._integrator.toReal + ki * dtc * (aE s tgt meas).toReal) 1.4e-10 := by
    have := near_add (Near32.exact hI) i3 (B := 0.001726) (bnd3 (by linarith) (by linarith))
      (by norm_num)
    rw [ecomm] at this
    have hb : 0 + 3.3e-11 + u32 * 0.001726 ≤ (1.4e-10 : ℝ) := by linarith only [hu]
    exact this.mono hb
  have hIM := val_imax
  have hnIM := (Float32.isFinite_neg pa.IMAX).2 hIM.1
  have hIMv : pa.IMAX.toReal = 13421773 / 16777216 := val_imax.2
  have hnIMv : (-pa.IMAX).toReal = -(13421773 / 16777216) := by rw [Float32.toReal_neg, hIMv]
  have i5 : aI s tgt meas = s._integrator + aE s tgt meas * pa.I * 1.0 * dtF := by
    rw [aI_eq]
    exact constrain_float_of_near i4 hnIM hIM.1 (by rw [hnIMv]; linarith) (by rw [hIMv]; linarith)
  have hI' : Near32 (aI s tgt meas) (s._integrator.toReal + ki * dtc * (aE s tgt meas).toReal)
      1.4e-10 := i5 ▸ i4
  have hI'b : |(aI s tgt meas).toReal| ≤ 0.001726 := by
    have := hI'.bound
    have : |s._integrator.toReal + ki * dtc * (aE s tgt meas).toReal| ≤ 0.001725 := by
      rw [← ecomm]; apply bnd <;> linarith
    linarith
  -- output
  have o1 : Near32 (aE s tgt meas * pa.P) ((aE s tgt meas).toReal * kp) 3.3e-9 := by
    have := near_mul_const hE'0 near_kp (Ra := 1.099) hE'b (by rw [hkp]; norm_num)
    refine this.mono ?_
    rw [abs_of_pos (show (0 : ℝ) < kp by rw [hkp]; norm_num), hkp]; norm_num; linarith
  have o2 := (o1.mul_one One_lit1).mul_one One_lit1
  have hZD : Z (aD s tgt meas * pa.D * 1.0 * 1.0) :=
    zero_mul_Z One_lit1.1 (zero_mul_Z One_lit1.1 (mul_zero_Z g5.1 Z_lit0))
  have o3 := o2.add_zero hZD
  have o4 : Near32 (aE s tgt meas * pa.P * 1.0 * 1.0 + aD s tgt meas * pa.D * 1.0 * 1.0 +
      aI s tgt meas) (kp * (aE s tgt meas).toReal + (aI s tgt meas).toReal) 6.7e-9 := by
    have hR : |(aE s tgt meas).toReal * kp + (aI s tgt meas).toReal| ≤ 0.0568 := by
      have : |(aE s tgt meas).toReal * kp| ≤ 0.055 := by
        rw [abs_mul, abs_of_pos (show (0 : ℝ) < kp by rw [hkp]; norm_num), hkp]; linarith
      calc _ ≤ |(aE s tgt meas).toReal * kp| + |(aI s tgt meas).toReal| := abs_add_le _ _
        _ ≤ _ := by linarith
    have := near_add o3 (Near32.exact hI'.1) (B := 0.0568 + 3.3e-9) (by linarith) (by norm_num)
    exact (this.congr (by ring)).mono (by linarith)
  obtain ⟨-, -, -, -, -, -, -, -, q9⟩ := pida_eval s ht.1 hm.1 hr
  rw [q9]
  exact ⟨hE1, hI', o4, t3.1, hT'b, g5.1, hD'b, mul_zero_Z t3.1 Z_lit0, by rw [aTD_eq]; exact mul_zero_Z td2.1 Z_lit0⟩

/-! ## The hover offset, `set_throttle_out` and the angle boost -/

/-- The hover throttle as the position controller reads it (`get_throttle_hover`, constrained to
`[0.125, 0.6875]`) is `MOT_THST_HOVER` itself. -/
theorem throttle_hover_eq (m : AP_Motors.Inputs) (h : m._throttle_hover = hoverF) :
    AP_Motors.get_throttle_hover m = hoverF := by
  unfold AP_Motors.get_throttle_hover; rw [h]
  apply constrain_float_of_near near_H
  · have : (0.125 : Float32).toModel.unpack = .finite .positive 8388608 (-26) (by decide) := by rfl
    exact (lit32 _ _ _ this).1
  · have : (0.6875 : Float32).toModel.unpack = .finite .positive 11534336 (-24) (by decide) := by rfl
    exact (lit32 _ _ _ this).1
  · have : (0.125 : Float32).toModel.unpack = .finite .positive 8388608 (-26) (by decide) := by rfl
    rw [(lit32 _ _ _ this).2, Hf_eq]; norm_num
  · have : (0.6875 : Float32).toModel.unpack = .finite .positive 11534336 (-24) (by decide) := by rfl
    rw [(lit32 _ _ _ this).2, Hf_eq]; norm_num

/-- The raise of `PSC_D_ACC_IMAX` to the hover throttle (`AC_PosControl.cpp:1127-1129`) is not
taken: `0.4444 < 0.8`. -/
theorem imax_raise_not_taken : ¬ (hoverF > AC_PID.imax pa) := by
  have : AC_PID.imax pa = AC_PosControl.POSCONTROL_D_ACC_IMAX := rfl
  rw [this]
  exact not_lt_of val_imax.1 near_H.1 (by rw [near_H.val0, val_imax.2, Hf_eq]; norm_num)

/-- **Hover offset.** The PID output within `6.7 · 10⁻⁹` of `r` (`|r| ≤ 0.0568`), plus the zero
feed-forward, minus `MOT_THST_HOVER`, negated: the throttle is within `3.7 · 10⁻⁸` of `H - r`. -/
theorem throttle_near {out ff : Float32} {r : ℝ} (ho : Near32 out r 6.7e-9) (hr : |r| ≤ 0.0568)
    (hff : Z ff) : Near32 (-(out + ff - hoverF)) (Hf - r) 3.7e-8 := by
  have hu := u32_le; have hu0 := u32_nonneg
  have hr' := abs_le.1 hr
  have e1 := ho.add_zero hff
  have e2 := near_sub e1 near_H (B := 0.5013) (bnd3 (by rw [Hf_eq]; linarith)
    (by rw [Hf_eq]; linarith)) (by norm_num)
  have e3 := near_neg e2
  exact (e3.congr (by ring)).mono (by linarith)

theorem constrain_float_hi {x lo hi : Float32} (hx : x.IsFinite) (hlo : lo.IsFinite)
    (hhi : hi.IsFinite) (hle : lo.toReal ≤ hi.toReal) (h : hi.toReal < x.toReal) :
    constrain_float x lo hi = hi := by
  show Float32Clip.constrain_float x lo hi = hi
  unfold Float32Clip.constrain_float
  rw [if_neg (Float32Clip.not_isNaN_of_isFinite hx), if_neg (not_lt_of hx hlo (by linarith))]
  have : x > hi := lt_true hhi hx h
  rw [if_pos this]

theorem lit10 : (10.0 : Float32).IsFinite ∧ (10.0 : Float32).toReal = 10 := by
  have : (10.0 : Float32).toModel.unpack = .finite .positive 10485760 (-20) (by decide) := by rfl
  obtain ⟨h1, h2⟩ := lit32 _ _ _ this
  exact ⟨h1, by rw [h2]; norm_num⟩

theorem lit01 : (0.1 : Float32).IsFinite ∧ (0.1 : Float32).toReal = 13421773 / 134217728 := by
  have : (0.1 : Float32).toModel.unpack = .finite .positive 13421773 (-27) (by decide) := by rfl
  obtain ⟨h1, h2⟩ := lit32 _ _ _ this
  exact ⟨h1, by rw [h2]; norm_num⟩

/-- **Angle boost at level.** With `cos pitch = cos roll = 1` and `cos(_thrust_angle_rad) = 1` (a C
library fact at `0`), `get_throttle_boosted` multiplies by `inverted_factor = constrain(10, 0, 1)
= 1` and `boost_factor = 1 / constrain(1, 0.1, 1) = 1`: the boosted throttle has the value of its
input, whether the boost is enabled or not. -/
theorem boosted_val (p : AC_AttitudeControl_Multi.Params) (s : AC_AttitudeControl_Multi.State)
    {cp cr thr : Float32} (hcp : One cp) (hcr : One cr) (hcos : One (Float32.cos s._thrust_angle_rad))
    (ht : thr.IsFinite) :
    (AC_AttitudeControl_Multi.get_throttle_boosted p s cp cr thr).2.IsFinite ∧
      (AC_AttitudeControl_Multi.get_throttle_boosted p s cp cr thr).2.toReal = thr.toReal := by
  unfold AC_AttitudeControl_Multi.get_throttle_boosted
  split
  · exact ⟨ht, rfl⟩
  · simp only
    have hct := mul_one_val hcp.1 hcr
    have hct' : One (cp * cr) := ⟨hct.1, by rw [hct.2, hcp.2]⟩
    have h10 := mul_one_val lit10.1 hct'
    have hinv : constrain_float ((10.0 : Float32) * (cp * cr)) 0.0 1.0 = 1.0 :=
      constrain_float_hi h10.1 Z_lit0.1 One_lit1.1 (by rw [Z_lit0.2, One_lit1.2]; norm_num)
        (by rw [h10.2, lit10.2, One_lit1.2]; norm_num)
    have hb : constrain_float (Float32.cos s._thrust_angle_rad) 0.1 1.0 =
        Float32.cos s._thrust_angle_rad :=
      constrain_float_of_le hcos.1 lit01.1 One_lit1.1 (by rw [lit01.2, hcos.2]; norm_num)
        (by rw [hcos.2, One_lit1.2])
    rw [hinv, hb]
    have hq := div_exact One_lit1.1 hcos.1 (by rw [hcos.2]; norm_num) One_lit1.1
      (by rw [One_lit1.2, hcos.2]; norm_num)
    have hq' : One ((1.0 : Float32) / Float32.cos s._thrust_angle_rad) := ⟨hq.1, by rw [hq.2, One_lit1.2]⟩
    have m1 := mul_one_val ht One_lit1
    have m2 := mul_one_val m1.1 hq'
    exact ⟨m2.1, by rw [m2.2, m1.2]⟩

/-- `update_althold_lean_angle_max` writes only `_althold_lean_angle_max_rad`. -/
theorem althold_thrust_angle (p : AC_AttitudeControl_Multi.Params) (s : AC_AttitudeControl_Multi.State)
    (m : AP_Motors.Inputs) (thr : Float32) :
    (AC_AttitudeControl_Multi.update_althold_lean_angle_max p s m thr)._thrust_angle_rad =
      s._thrust_angle_rad := by
  unfold AC_AttitudeControl_Multi.update_althold_lean_angle_max
  dsimp only
  split <;> rfl

/-- **`set_throttle_out` at level.** With the angle boost applied (as `D_update_controller` asks),
the motors' `_throttle_in` has the value of the throttle passed in, its filter cutoff is the one
passed in, and the attitude controller stores the throttle. -/
theorem set_throttle_out_val (p : AC_AttitudeControl_Multi.Params)
    (s : AC_AttitudeControl_Multi.State) (m : AP_Motors.Inputs) {cp cr thr c : Float32}
    (hcp : One cp) (hcr : One cr) (hcos : One (Float32.cos s._thrust_angle_rad))
    (ht : thr.IsFinite) :
    (AC_AttitudeControl_Multi.set_throttle_out p s m cp cr thr true c).2._throttle_in.IsFinite ∧
      (AC_AttitudeControl_Multi.set_throttle_out p s m cp cr thr true c).2._throttle_in.toReal =
        thr.toReal ∧
      (AC_AttitudeControl_Multi.set_throttle_out p s m cp cr thr true c).2._throttle_filter_cutoff
        = c := by
  have h1 : (AC_AttitudeControl_Multi.set_throttle_out p s m cp cr thr true c).2._throttle_in =
      (AC_AttitudeControl_Multi.get_throttle_boosted p
        (AC_AttitudeControl_Multi.update_althold_lean_angle_max p { s with _throttle_in := thr } m thr)
        cp cr thr).2 := rfl
  have h2 : (AC_AttitudeControl_Multi.set_throttle_out p s m cp cr thr true c).2._throttle_filter_cutoff
      = c := rfl
  have hcos' : One (Float32.cos (AC_AttitudeControl_Multi.update_althold_lean_angle_max p
      { s with _throttle_in := thr } m thr)._thrust_angle_rad) := by
    rw [althold_thrust_angle]; exact hcos
  rw [h1, h2]
  exact ⟨(boosted_val p _ hcp hcr hcos' ht).1, (boosted_val p _ hcp hcr hcos' ht).2, rfl⟩

/-! ## The motors' throttle filter `update_throttle_filter` (2 Hz) -/

/-- **Throttle filter.** With the cutoff at `2 Hz` (set by `set_throttle_out`), the motors' period
`dtF`, the filter output `F` of value `4/9 + φ` and the stored throttle within `3.7 · 10⁻⁸` of
`4/9 + τ` (`|φ| ≤ 1/100`, `|τ| ≤ 0.0665`): the new filter output is within `2.9 · 10⁻⁸` of
`4/9 + (1 - am) φ + am τ` (the `φ'` line of `stepN` with `τ = -kp Ea - ι`, so `|n4| ≤ 2.9 · 10⁻⁸`),
and the clip to `[0, 1]` is inactive. Nothing else changes. -/
theorem throttle_filter_near (s : AP_MotorsMulticopter.State) {φ τ : ℝ}
    (hc : s._throttle_filter_cutoff = AC_PosControl.POSCONTROL_THROTTLE_CUTOFF_FREQ_HZ)
    (hdt : s._dt_s = dtF)
    (hF : Near32 s._throttle_filter_value (4 / 9 + φ) 0)
    (hT : Near32 s._throttle_in (4 / 9 + τ) 3.7e-8)
    (hφ : |φ| ≤ 1 / 100) (hτ : |τ| ≤ 0.0665) :
    AP_MotorsMulticopter.update_throttle_filter s =
        { s with _throttle_filter_value := s._throttle_filter_value +
            (s._throttle_in - s._throttle_filter_value) *
              calc_lowpass_alpha_dt dtF AC_PosControl.POSCONTROL_THROTTLE_CUTOFF_FREQ_HZ } ∧
      Near32 (s._throttle_filter_value + (s._throttle_in - s._throttle_filter_value) *
          calc_lowpass_alpha_dt dtF AC_PosControl.POSCONTROL_THROTTLE_CUTOFF_FREQ_HZ)
        (4 / 9 + ((1 - am) * φ + am * τ)) 2.9e-8 := by
  have hu := u32_le; have hu0 := u32_nonneg; have hη := η32_le; have hη0 := η32_nonneg
  have hφ' := abs_le.1 hφ; have hτ' := abs_le.1 hτ
  have ham := am_eq
  have d1 : Near32 (s._throttle_in - s._throttle_filter_value) (τ - φ) 4.2e-8 := by
    have := near_sub hT hF (B := 0.07651) (bnd3 (by linarith) (by linarith)) (by norm_num)
    exact (this.congr (by ring)).mono (by linarith)
  have d2 : Near32 ((s._throttle_in - s._throttle_filter_value) *
      calc_lowpass_alpha_dt dtF AC_PosControl.POSCONTROL_THROTTLE_CUTOFF_FREQ_HZ) ((τ - φ) * am)
      1.5e-9 := by
    have := near_mul_const d1 near_am (Ra := 0.0765) (bnd (by linarith) (by linarith))
      (by rw [abs_of_pos (show (0 : ℝ) < am by rw [ham]; norm_num), ham]; norm_num)
    refine this.mono ?_
    rw [abs_of_pos (show (0 : ℝ) < am by rw [ham]; norm_num), ham]
    linarith
  have d3 : Near32 (s._throttle_filter_value + (s._throttle_in - s._throttle_filter_value) *
      calc_lowpass_alpha_dt dtF AC_PosControl.POSCONTROL_THROTTLE_CUTOFF_FREQ_HZ)
      (4 / 9 + ((1 - am) * φ + am * τ)) 2.9e-8 := by
    have hR : |4 / 9 + φ + (τ - φ) * am| + 0 + 1.5e-9 ≤ 0.4563 := by
      rw [ham]; apply bnd3 <;> linarith
    have := near_add hF d2 hR (by norm_num)
    exact (this.congr (by ring)).mono (by linarith)
  refine ⟨?_, d3⟩
  have hlo := d3.lo; have hhi := d3.hi
  have c1 : ¬ (s._throttle_filter_value + (s._throttle_in - s._throttle_filter_value) *
      calc_lowpass_alpha_dt dtF AC_PosControl.POSCONTROL_THROTTLE_CUTOFF_FREQ_HZ) < 0.0 :=
    not_lt_of d3.1 Z_lit0.1 (by rw [Z_lit0.2]; rw [ham] at hlo; linarith)
  have c2 : ¬ (s._throttle_filter_value + (s._throttle_in - s._throttle_filter_value) *
      calc_lowpass_alpha_dt dtF AC_PosControl.POSCONTROL_THROTTLE_CUTOFF_FREQ_HZ) > 1.0 :=
    not_lt_of One_lit1.1 d3.1 (by rw [One_lit1.2]; rw [ham] at hhi; linarith)
  simp only [AP_MotorsMulticopter.update_throttle_filter, AP_MotorsMulticopter.LowPassFilterFloat_apply,
    hc, hdt, Id.run]
  simp only [c1, c2, if_false]
  rfl

/-! ## The thrust curve and the slew limit in the linear configuration -/

/-- The linear thrust configuration (`sim/params/copter-cf2x.txt`): `MOT_THST_EXPO 0`,
`MOT_SPIN_MIN 0`, `MOT_SPIN_MAX 1`, and no slew limiting (`MOT_SLEW_UP_TIME`, `MOT_SLEW_DN_TIME`
not positive, the code defaults). -/
-- <<LinearConfig>>
structure LinearConfig (p : AP_MotorsMulticopter.Params) : Prop where
  expo : Z p.MOT_THST_EXPO
  spin_min : Z p.MOT_SPIN_MIN
  spin_max : One p.MOT_SPIN_MAX
  slew_up : is_positive p.MOT_SLEW_UP_TIME = false
  slew_dn : is_positive p.MOT_SLEW_DN_TIME = false
-- <</LinearConfig>>

/-- The run's `MOT_` parameters: the code defaults with the overrides of `Copter.defaults` and of
`sim/params/copter-cf2x.txt` (`MOT_THST_EXPO 0`, `MOT_SPIN_MIN 0`, `MOT_SPIN_MAX 1`,
`MOT_BAT_VOLT_MAX 0`, `MOT_HOVER_LEARN 0`, `MOT_THST_HOVER 0.4444`). -/
def runMot : AP_MotorsMulticopter.Params :=
  { Copter.defaults.mot with
    MOT_THST_EXPO := Copter.Text.Decimal.toFloat32 ⟨false, 0, 0⟩
    MOT_SPIN_MIN := Copter.Text.Decimal.toFloat32 ⟨false, 0, 0⟩
    MOT_SPIN_MAX := Copter.Text.Decimal.toFloat32 ⟨false, 1, 0⟩
    MOT_BAT_VOLT_MAX := Copter.Text.Decimal.toFloat32 ⟨false, 0, 0⟩
    MOT_HOVER_LEARN := 0
    MOT_THST_HOVER := Copter.Text.Decimal.toFloat32 ⟨false, 4444, -4⟩ }

theorem runMot_hover : runMot.MOT_THST_HOVER = hoverF := by rfl

/-- The run parameters are in the linear configuration. -/
theorem runMot_linear : LinearConfig runMot := by
  have h0 : (Copter.Text.Decimal.toFloat32 ⟨false, 0, 0⟩).toModel.unpack = .zero .positive := by rfl
  have h1 : (Copter.Text.Decimal.toFloat32 ⟨false, 1, 0⟩).toModel.unpack =
      (1 : Float32).toModel.unpack := by rfl
  have z0 : Z (Copter.Text.Decimal.toFloat32 ⟨false, 0, 0⟩) := by
    refine ⟨by rw [Float32.isFinite_iff, h0]; rfl, ?_⟩
    rw [Float32.toReal, h0]; rfl
  have o1 : One (Copter.Text.Decimal.toFloat32 ⟨false, 1, 0⟩) := by
    refine ⟨by rw [Float32.isFinite_iff, h1]; exact Float32.isFinite_one, ?_⟩
    rw [Float32.toReal, h1]; exact Float32.toReal_one
  exact ⟨z0, z0, o1, by decide, by decide⟩

/-- **Thrust curve.** In the linear configuration, with `lift_max = 1` and the battery filter at
`1` (what `update_lift_max_from_batt_voltage` writes every tick), `thrust_to_actuator` is the
identity on `[0, 1]`: `0 + (1 - 0) · (1 · t · (1/1)) = t`. -/
theorem thrust_to_actuator_val {p : AP_MotorsMulticopter.Params} (hp : LinearConfig p)
    {t : Float32} (ht : t.IsFinite) (h0 : 0 ≤ t.toReal) (h1 : t.toReal ≤ 1) :
    (Thrust_Linearization.thrust_to_actuator p.toParams
        { lift_max := 1.0, batt_voltage_filt := 1.0 } t).IsFinite ∧
      (Thrust_Linearization.thrust_to_actuator p.toParams
        { lift_max := 1.0, batt_voltage_filt := 1.0 } t).toReal = t.toReal := by
  unfold Thrust_Linearization.thrust_to_actuator Thrust_Linearization.apply_thrust_curve_and_volt_scaling
  have hc : constrain_float t 0.0 1.0 = t :=
    constrain_float_of_le ht Z_lit0.1 One_lit1.1 (by rw [Z_lit0.2]; exact h0)
      (by rw [One_lit1.2]; exact h1)
  have hneg1 : ((-1.0 : Float32)).IsFinite ∧ ((-1.0 : Float32)).toReal = -1 := by
    have := One_lit1
    exact ⟨(Float32.isFinite_neg _).2 this.1, by rw [Float32.toReal_neg, this.2]⟩
  have he : constrain_float p.MOT_THST_EXPO (-1.0) 1.0 = p.MOT_THST_EXPO :=
    constrain_float_of_le hp.expo.1 hneg1.1 One_lit1.1 (by rw [hneg1.2, hp.expo.2]; norm_num)
      (by rw [One_lit1.2, hp.expo.2]; norm_num)
  have hz : is_zero p.MOT_THST_EXPO = true := is_zero_true hp.expo.1 (by rw [hp.expo.2]; norm_num)
  have hpos : is_positive (1.0 : Float32) = true := by decide
  simp only [Id.run, pure, hc, he, hz, hpos, if_true]
  have hq : One ((1.0 : Float32) / 1.0) := by
    have := div_exact One_lit1.1 One_lit1.1 (by rw [One_lit1.2]; norm_num) One_lit1.1
      (by rw [One_lit1.2]; norm_num)
    exact ⟨this.1, by rw [this.2, One_lit1.2]⟩
  have m1 := one_mul_val ht One_lit1
  have m2 := mul_one_val m1.1 hq
  have d := sub_zero_val hp.spin_max.1 hp.spin_min
  have d' : One (p.MOT_SPIN_MAX - p.MOT_SPIN_MIN) := ⟨d.1, by rw [d.2, hp.spin_max.2]⟩
  have m3 := one_mul_val m2.1 d'
  have a := zero_add_val m3.1 hp.spin_min
  exact ⟨a.1, by rw [a.2, m3.2, m2.2, m1.2]⟩

/-- **Slew limit off.** With both slew times not positive, `set_actuator_with_slew` is
`constrain_float(input, 0, 1)`, which on `[0, 1]` is the input. -/
theorem slew_val {p : AP_MotorsMulticopter.Params} (hp : LinearConfig p)
    (st : AP_MotorsMulticopter.State) (a : Float32) {x : Float32} (hx : x.IsFinite)
    (h0 : 0 ≤ x.toReal) (h1 : x.toReal ≤ 1) :
    AP_MotorsMulticopter.set_actuator_with_slew p st a x = x := by
  unfold AP_MotorsMulticopter.set_actuator_with_slew
  simp only [Id.run, hp.slew_up, hp.slew_dn, Bool.false_eq_true, if_false]
  exact constrain_float_of_le hx Z_lit0.1 One_lit1.1 (by rw [Z_lit0.2]; exact h0)
    (by rw [One_lit1.2]; exact h1)

theorem finRange4 : List.finRange 4 = [0, 1, 2, 3] := by decide
theorem en4_0 : (#v[true, true, true, true] : Vector Bool 4)[(0 : Fin 4)] = true := rfl
theorem en4_1 : (#v[true, true, true, true] : Vector Bool 4)[(1 : Fin 4)] = true := rfl
theorem en4_2 : (#v[true, true, true, true] : Vector Bool 4)[(2 : Fin 4)] = true := rfl
theorem en4_3 : (#v[true, true, true, true] : Vector Bool 4)[(3 : Fin 4)] = true := rfl

/-- Four `set`s at the four slots: every slot holds one of the values set. -/
theorem set4_get {α : Type} (v : Vector α 4) (x : Fin 4 → α) (h0 h1 h2 h3)
    (P : α → Prop) (hP : ∀ i, P (x i)) (i : Fin 4) :
    P ((((v.set ((0 : Fin 4) : ℕ) (x 0) h0).set ((1 : Fin 4) : ℕ) (x 1) h1).set ((2 : Fin 4) : ℕ)
      (x 2) h2).set ((3 : Fin 4) : ℕ) (x 3) h3)[i] := by
  fin_cases i <;> simp [Vector.getElem_set] <;> exact hP _

/-- **Actuators.** With the four motors enabled, the linear configuration, `lift_max = 1` and the
battery filter at `1`, and the four thrusts `_thrust_rpyt_out[i]` of value `t ∈ [0, 1]`,
`output_to_motors` sets each actuator to a float of value `t` (`thrust_to_actuator` is the
identity and the slew limit is off). -/
theorem output_to_motors_val {p : AP_MotorsMulticopter.Params} (hp : LinearConfig p)
    (s : AP_MotorsMatrix.State) (hen : s.motor_enabled = #v[true, true, true, true])
    (hthr : s.thr_lin = { lift_max := 1.0, batt_voltage_filt := 1.0 }) {t : ℝ}
    (h0 : 0 ≤ t) (h1 : t ≤ 1)
    (hT : ∀ i : Fin 4, (s._thrust_rpyt_out[i]).IsFinite ∧ (s._thrust_rpyt_out[i]).toReal = t) :
    ∀ i : Fin 4, ((AP_MotorsMatrix.output_to_motors p s).2[i]).IsFinite ∧
      ((AP_MotorsMatrix.output_to_motors p s).2[i]).toReal = t := by
  have key : ∀ i : Fin 4, ∀ a : Float32,
      AP_MotorsMulticopter.set_actuator_with_slew p s.toState a
        (Thrust_Linearization.thrust_to_actuator p.toParams s.thr_lin s._thrust_rpyt_out[i]) =
      Thrust_Linearization.thrust_to_actuator p.toParams s.thr_lin s._thrust_rpyt_out[i] := by
    intro i a
    rw [hthr]
    obtain ⟨hf, hv⟩ := hT i
    have := thrust_to_actuator_val hp hf (by rw [hv]; exact h0) (by rw [hv]; exact h1)
    exact slew_val hp _ a this.1 (by rw [this.2, hv]; exact h0) (by rw [this.2, hv]; exact h1)
  have val : ∀ i : Fin 4,
      (Thrust_Linearization.thrust_to_actuator p.toParams s.thr_lin s._thrust_rpyt_out[i]).IsFinite ∧
      (Thrust_Linearization.thrust_to_actuator p.toParams s.thr_lin s._thrust_rpyt_out[i]).toReal = t := by
    intro i
    rw [hthr]
    obtain ⟨hf, hv⟩ := hT i
    have := thrust_to_actuator_val hp hf (by rw [hv]; exact h0) (by rw [hv]; exact h1)
    exact ⟨this.1, this.2.trans hv⟩
  unfold AP_MotorsMatrix.output_to_motors
  simp only [Id.run, pure, bind, finRange4, List.forIn_cons, List.forIn_nil, hen, en4_0, en4_1,
    en4_2, en4_3, if_true, key]
  intro i
  exact set4_get _ (fun j => Thrust_Linearization.thrust_to_actuator p.toParams s.thr_lin
    s._thrust_rpyt_out[j]) _ _ _ _ (fun y => y.IsFinite ∧ y.toReal = t) val i

end

end Contracts.CopterVertNear
