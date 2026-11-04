import Contracts.CopterVertNearTick

/-!
# The first tick of the vertical channel: both PIDs in reset

`Contracts.CopterVertNear.vert_tick` follows one tick of the vertical path with the velocity and
acceleration PIDs out of reset. The first tick of the hover (just after `D_init_controller`) runs
the same composition with both PIDs in reset (`_reset_filter = true`): the error filters are set
to the raw errors, the derivative filters to `0`, and the acceleration integrator integrates the
raw error once from the zero that `D_init_controller` stores. This file shows that after that tick
the exact values of the floats lie in the sublevel set `V ≤ 1/10` of `Contracts.CopterVert` and
satisfy the tick invariant `VInv`, so that `vert_tick` applies from the second tick on.

**The first tick.** The harness stores `_throttle_in = _throttle_filter_value` of value
`H = 0.4444` (binary32), so the motors' filter keeps its value exactly (`F + (F - F) α = F`). The
position target is the navigator's stopping point, within `10⁻⁶` of `-1` (binary64), the position
reading within `10⁻¹⁵` of `-1`, the velocity reading a zero and the specific force reading within
`6 · 10⁻⁷` of `-k H`. Then:

* the velocity target and the velocity error filter are within `1.01 · 10⁻⁶` of `0`
  (`p1d_near0`, `pidv_near0`);
* the acceleration error filter is within `8 · 10⁻⁷` of `kv Ev + k I*` (`I* = H - 4/9`, so
  `Ea ≈ -9.8 · 10⁻⁴`), the integrator within `10⁻¹³` of `ki dtc Ea` (`≈ -2.4 · 10⁻⁷`), and the
  output within `6.7 · 10⁻⁹` of `kp Ea + I` (`pida_near0`);
* the plant moves from `ζ = 0`, `w = 0` with the actuator `H`: `ζ' = 0`, `w' = -k h I*`
  (`≈ 2.45 · 10⁻⁶ m/s`, NED).

The new exact state has `|ζ| = 0`, `|w| ≤ 10⁻⁵`, `|Ev| ≤ 10⁻⁵`, `|Ea| ≤ 10⁻²`, `|ι| ≤ 10⁻⁴`,
`|φ| ≤ 10⁻⁴`, on which `V ≤ 1/400` (`V_first`).
-/

open Float.Model UnpackedFloat AP_Math Contracts.CopterVert Contracts.CopterVertNear

namespace Contracts.CopterHover

noncomputable section

attribute [local irreducible] av aa am kp ki kv kpos dtc g k CopterVert.h Gf Hf

/-- The exact value of `I* = H - 4/9`. -/
theorem Istar_val : Istar = -(6709 / 150994944) := by
  rw [Istar, Hf_eq]; norm_num

/-! ## The position P controller with the stopping point as target -/

/-- **Position loop at the stopping point.** With the target within `10⁻⁶` of `-1` and the position
reading within `10⁻¹⁵` of `-1` (binary64), and the error limits and `D1_max` at least `1 cm` away,
the narrowed error and the velocity target are within `1.01 · 10⁻⁶` of `0`; no clamp applies and
the target is returned unchanged. -/
theorem p1d_near0 (hN : NarrowSpec 1) (s : AC_P_1D.State) {tgt meas : Float}
    (htgt : Near64 tgt (-1) 1e-6) (hmeas : Near64 meas (-1) 1e-15)
    (hmin : s._error_min.IsFinite) (hmin' : s._error_min.toReal ≤ -(1 / 100))
    (hmax : s._error_max.IsFinite) (hmax' : 1 / 100 ≤ s._error_max.toReal)
    (hD1 : s._D1_max.IsFinite) (hD1' : 1 / 100 ≤ s._D1_max.toReal) :
    Near32 (AC_P_1D.update_all ⟨AC_PosControl.POSCONTROL_D_POS_P⟩ s tgt meas).2.2 0 1.01e-6 ∧
      (AC_P_1D.update_all ⟨AC_PosControl.POSCONTROL_D_POS_P⟩ s tgt meas).2.1 = tgt ∧
      Near32 (AC_P_1D.update_all ⟨AC_PosControl.POSCONTROL_D_POS_P⟩ s tgt meas).1._error
        0 1.01e-6 := by
  have hu := u32_le; have hu0 := u32_nonneg; have hη := η32_le; have hη0 := η32_nonneg
  -- binary64 difference and narrowing
  have e1 : Near64 (tgt - meas) 0 1.0001e-6 := by
    have := near64_sub htgt hmeas (B := 1.0001e-6) (by norm_num) (by norm_num)
    refine ⟨this.1, ?_⟩
    have h2 := this.2
    rw [show (-1 : ℝ) - -1 = 0 by ring] at h2
    refine h2.trans ?_
    have : (2 : ℝ) ^ (-53 : ℤ) * 1.0001e-6 ≤ 1e-21 := by norm_num
    linarith
  have e2 : Near32 (tofloat (tgt - meas)) 0 1.01e-6 := by
    have := near_narrow hN e1 (by norm_num)
    refine this.mono ?_
    rw [abs_zero, zero_add]
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
    have hnld :=
      (Float32.isFinite_neg (s._D1_max / AP_Math.sq AC_PosControl.POSCONTROL_D_POS_P)).2 hld.1
    have b4 : ¬ err < -(s._D1_max / AP_Math.sq AC_PosControl.POSCONTROL_D_POS_P) :=
      not_lt_of e2.1 hnld (by rw [Float32.toReal_neg, hld.2]; linarith)
    have b5 : is_positive (0.0 : Float32) = false := by decide
    simp only [b1, b2, b5, Bool.false_eq_true, if_false]
    show (if err > s._D1_max / AP_Math.sq AC_PosControl.POSCONTROL_D_POS_P then _ else
      if err < -(s._D1_max / AP_Math.sq AC_PosControl.POSCONTROL_D_POS_P) then _ else _) = _
    rw [if_neg b3, if_neg b4]
  have hout : Near32 (err * AC_PosControl.POSCONTROL_D_POS_P) 0 1.01e-6 := e2.mul_one one_p
  simp only [AC_P_1D.update_all, ← herr, c1, c2, Bool.false_eq_true, if_false, Id.run, hsc]
  exact ⟨hout, rfl, e2⟩

/-! ## The velocity PID in reset -/

/-- The velocity PID in reset, written out: the error filter is set to `target - measurement`,
the derivative filter to `0`, the integrator to `0` (`I = 0`), and the output is
`P_out + I + D_out + FF_out`. -/
theorem pidv_eval0 (s : AC_PID_Basic.State) {tgt meas : Float32} (ht : tgt.IsFinite)
    (hm : meas.IsFinite) (hr : s._reset_filter = true) (ln lp : Bool) :
    (AC_PID_Basic.update_all pv s tgt meas dtF ln lp).1._error = tgt - meas ∧
    (AC_PID_Basic.update_all pv s tgt meas dtF ln lp).1._integrator = 0.0 ∧
    (AC_PID_Basic.update_all pv s tgt meas dtF ln lp).1._reset_filter = false ∧
    (AC_PID_Basic.update_all pv s tgt meas dtF ln lp).1._derivative = 0.0 ∧
    (AC_PID_Basic.update_all pv s tgt meas dtF ln lp).2 =
      (tgt - meas) * pv.P + 0.0 + 0.0 * pv.D + tgt * pv.FF := by
  simp only [AC_PID_Basic.update_all, AC_PID_Basic.update_i, isFinite_true ht, isFinite_true hm,
    not_isNaN ht, not_isNaN hm, hr, pv_I]
  simp

/-- **Velocity loop in reset.** With the velocity target within `1.01 · 10⁻⁶` of `0` and the
velocity reading a zero: the new error filter has the value of the target (within
`1.01 · 10⁻⁶` of `0`), the integrator is `0`, the PID leaves reset, the derivative filter is `0`,
and the output is within `10⁻¹²` of `kv E'` with `E'` the exact value of the new error filter. -/
theorem pidv_near0 (s : AC_PID_Basic.State) {tgt meas : Float32} (hr : s._reset_filter = true)
    (ht : Near32 tgt 0 1.01e-6) (hm : Z meas) (ln lp : Bool) :
    Near32 (AC_PID_Basic.update_all pv s tgt meas dtF ln lp).1._error 0 1.01e-6 ∧
      Z (AC_PID_Basic.update_all pv s tgt meas dtF ln lp).1._integrator ∧
      (AC_PID_Basic.update_all pv s tgt meas dtF ln lp).1._reset_filter = false ∧
      (AC_PID_Basic.update_all pv s tgt meas dtF ln lp).1._derivative.IsFinite ∧
      |(AC_PID_Basic.update_all pv s tgt meas dtF ln lp).1._derivative.toReal| ≤ 3 ∧
      Near32 (AC_PID_Basic.update_all pv s tgt meas dtF ln lp).2
        (kv * (AC_PID_Basic.update_all pv s tgt meas dtF ln lp).1._error.toReal) 1e-12 := by
  obtain ⟨q1, q2, q3, q4, q5⟩ := pidv_eval0 s ht.1 hm.1 hr ln lp
  rw [q1, q2, q3, q4, q5]
  have hu := u32_le; have hu0 := u32_nonneg; have hη := η32_le; have hη0 := η32_nonneg
  have hE := sub_zero_val ht.1 hm
  have hE1 : Near32 (tgt - meas) 0 1.01e-6 := Near32.of_eq_val hE.1 hE.2 ht
  have hEb : |(tgt - meas).toReal| ≤ 1.01e-6 := by
    have := hE1.bound; rw [abs_zero, zero_add] at this; exact this
  have o1 : Near32 ((tgt - meas) * pv.P) ((tgt - meas).toReal * kv) 1e-12 := by
    rw [pv_P]
    have := near_mul_const (Near32.exact hE1.1) near_kv (Ra := 1.01e-6) hEb
      (by rw [kv_eq]; norm_num)
    refine this.mono ?_
    rw [kv_eq]; norm_num; linarith
  have o2 := ((o1.add_zero Z_lit0).add_zero (mul_zero_Z Z_lit0.1 Z_pv_D)).add_zero
    (mul_zero_Z ht.1 Z_pv_FF)
  exact ⟨hE1, Z_lit0, rfl, Z_lit0.1, by rw [Z_lit0.2]; norm_num, o2.congr (by ring)⟩

/-! ## The acceleration PID in reset -/

/-- The new integrator of the acceleration PID in reset: one step from the stored one with the
raw error, clamped to `±IMAX`. -/
def bI (s : AC_PID.State) (tgt meas : Float32) : Float32 :=
  constrain_float (s._integrator + (tgt - meas) * pa.I * 1.0 * dtF) (-pa.IMAX) pa.IMAX

theorem bI_eq (s : AC_PID.State) (tgt meas : Float32) :
    bI s tgt meas =
      constrain_float (s._integrator + (tgt - meas) * pa.I * 1.0 * dtF) (-pa.IMAX) pa.IMAX := rfl

/-- The acceleration PID in reset with `limit = false`, written out: the target and error filters
are set to the target and the raw error, the derivative and target derivative to `0`, and the
integrator integrates the raw error once. -/
theorem pida_eval0 (s : AC_PID.State) {tgt meas : Float32} (ht : tgt.IsFinite)
    (hm : meas.IsFinite) (hr : s._flags._reset_filter = true) :
    (AC_PID.update_all pa s tgt meas dtF false).1._target = tgt ∧
    (AC_PID.update_all pa s tgt meas dtF false).1._error = tgt - meas ∧
    (AC_PID.update_all pa s tgt meas dtF false).1._derivative = 0.0 ∧
    (AC_PID.update_all pa s tgt meas dtF false).1._target_derivative = 0.0 ∧
    (AC_PID.update_all pa s tgt meas dtF false).1._integrator = bI s tgt meas ∧
    (AC_PID.update_all pa s tgt meas dtF false).1._flags._reset_filter = false ∧
    (AC_PID.update_all pa s tgt meas dtF false).1._pid_info.FF = tgt * pa.FF ∧
    (AC_PID.update_all pa s tgt meas dtF false).1._pid_info.DFF = 0.0 * pa.D_FF ∧
    (AC_PID.update_all pa s tgt meas dtF false).2 =
      (tgt - meas) * pa.P * 1.0 * 1.0 + 0.0 * pa.D * 1.0 * 1.0 + bI s tgt meas := by
  simp only [AC_PID.update_all, AC_PID.update_i, isFinite_true ht, isFinite_true hm, hr, pos_dtF,
    pa_I, pa_PDMX]
  simp [bI, AC_PID.slew_limiter_modifier_smax_off]

attribute [irreducible] bI

/-- **Acceleration loop in reset.** With the stored integrator a zero, the target within
`10⁻¹²` of `A` (`|A| ≤ 6 · 10⁻⁶`) and the measurement within `7.8 · 10⁻⁷` of `-k I*`: the raw
error is within `8 · 10⁻⁷` of `A + k I*`, the new integrator within `10⁻¹³` of `ki dtc E` (`E` the
exact value of the raw error; the clamp is inactive), and the output within `6.7 · 10⁻⁹` of
`kp E + I'` (`I'` the exact value of the new integrator). -/
theorem pida_near0 (s : AC_PID.State) {tgt meas : Float32} {A : ℝ}
    (hr : s._flags._reset_filter = true) (hI : Z s._integrator)
    (ht : Near32 tgt A 1e-12) (hA : |A| ≤ 6e-6) (hm : Near32 meas (-(k * Istar)) 7.8e-7) :
    Near32 (tgt - meas) (A + k * Istar) 8e-7 ∧
      Near32 (bI s tgt meas) (ki * dtc * (tgt - meas).toReal) 1e-13 ∧
      Near32 (AC_PID.update_all pa s tgt meas dtF false).2
        (kp * (tgt - meas).toReal + (bI s tgt meas).toReal) 6.7e-9 := by
  have hu := u32_le; have hu0 := u32_nonneg; have hη := η32_le; have hη0 := η32_nonneg
  have hA' := abs_le.1 hA
  have hIs := Istar_val
  have hk := k_eq
  have hdtc := dtc_eq
  have hd0 : (0 : ℝ) < dtc := by rw [hdtc]; norm_num
  have hkp := kp_eq
  have hki := ki_eq
  -- the raw error
  have hE1 : Near32 (tgt - meas) (A + k * Istar) 8e-7 := by
    have := near_sub ht hm (B := 9.9e-4) (bnd3 (by rw [hk, hIs]; linarith)
      (by rw [hk, hIs]; linarith)) (by norm_num)
    exact (this.congr (by ring)).mono (by linarith)
  have hEb : |(tgt - meas).toReal| ≤ 9.9e-4 := by
    have := hE1.bound
    have : |A + k * Istar| ≤ 9.87e-4 := by rw [hk, hIs]; apply bnd <;> linarith
    linarith
  have hEb' := abs_le.1 hEb
  have hE0 := Near32.exact hE1.1
  -- the integrator
  have i1 : Near32 ((tgt - meas) * pa.I) ((tgt - meas).toReal * ki) 1e-11 := by
    have := near_mul_const hE0 near_ki (Ra := 9.9e-4) hEb (by rw [hki]; norm_num)
    refine this.mono ?_
    rw [abs_of_pos (show (0 : ℝ) < ki by rw [hki]; norm_num), hki]; norm_num; linarith
  have i2 := i1.mul_one One_lit1
  have i3 : Near32 ((tgt - meas) * pa.I * 1.0 * dtF) ((tgt - meas).toReal * ki * dtc) 1e-13 := by
    have hR : |(tgt - meas).toReal * ki| ≤ 1e-4 := by
      rw [abs_mul, abs_of_pos (show (0 : ℝ) < ki by rw [hki]; norm_num), hki]; linarith
    have := near_mul_const i2 near_dtF (Ra := 1e-4) hR (by rw [abs_of_pos hd0, hdtc]; norm_num)
    refine this.mono ?_
    rw [abs_of_pos hd0, hdtc]; norm_num; linarith
  have i4 := i3.zero_add hI
  have hIn : |(tgt - meas).toReal * ki * dtc| ≤ 2.5e-7 := by
    rw [abs_mul, abs_mul, abs_of_pos (show (0 : ℝ) < ki by rw [hki]; norm_num), abs_of_pos hd0,
      hki, hdtc]
    nlinarith [abs_nonneg (tgt - meas).toReal]
  have hIn' := abs_le.1 hIn
  have ecomm : (tgt - meas).toReal * ki * dtc = ki * dtc * (tgt - meas).toReal := by ring
  have hIM := val_imax
  have hnIM := (Float32.isFinite_neg pa.IMAX).2 hIM.1
  have hIMv : pa.IMAX.toReal = 13421773 / 16777216 := val_imax.2
  have hnIMv : (-pa.IMAX).toReal = -(13421773 / 16777216) := by rw [Float32.toReal_neg, hIMv]
  have i5 : bI s tgt meas = s._integrator + (tgt - meas) * pa.I * 1.0 * dtF := by
    rw [bI_eq]
    exact constrain_float_of_near i4 hnIM hIM.1 (by rw [hnIMv]; linarith) (by rw [hIMv]; linarith)
  have hI' : Near32 (bI s tgt meas) (ki * dtc * (tgt - meas).toReal) 1e-13 := by
    rw [i5, ← ecomm]; exact i4
  have hI'b : |(bI s tgt meas).toReal| ≤ 2.6e-7 := by
    have := hI'.bound; rw [← ecomm] at this; linarith
  -- the output
  have o1 : Near32 ((tgt - meas) * pa.P) ((tgt - meas).toReal * kp) 1e-11 := by
    have := near_mul_const hE0 near_kp (Ra := 9.9e-4) hEb (by rw [hkp]; norm_num)
    refine this.mono ?_
    rw [abs_of_pos (show (0 : ℝ) < kp by rw [hkp]; norm_num), hkp]; norm_num; linarith
  have o2 := (o1.mul_one One_lit1).mul_one One_lit1
  have hZD : Z ((0.0 : Float32) * pa.D * 1.0 * 1.0) :=
    zero_mul_Z One_lit1.1 (zero_mul_Z One_lit1.1 (mul_zero_Z Z_lit0.1 Z_lit0))
  have o3 := o2.add_zero hZD
  have o4 : Near32 ((tgt - meas) * pa.P * 1.0 * 1.0 + 0.0 * pa.D * 1.0 * 1.0 + bI s tgt meas)
      (kp * (tgt - meas).toReal + (bI s tgt meas).toReal) 6.7e-9 := by
    have hR : |(tgt - meas).toReal * kp + (bI s tgt meas).toReal| ≤ 1e-4 := by
      have : |(tgt - meas).toReal * kp| ≤ 5e-5 := by
        rw [abs_mul, abs_of_pos (show (0 : ℝ) < kp by rw [hkp]; norm_num), hkp]; linarith
      calc _ ≤ |(tgt - meas).toReal * kp| + |(bI s tgt meas).toReal| := abs_add_le _ _
        _ ≤ _ := by linarith
    have := near_add o3 (Near32.exact hI'.1) (B := 1e-4 + 1e-11) (by linarith) (by norm_num)
    exact (this.congr (by ring)).mono (by linarith)
  obtain ⟨-, -, -, -, -, -, -, -, q9⟩ := pida_eval0 s ht.1 hm.1 hr
  rw [q9]
  exact ⟨hE1, hI', o4⟩

/-! ## The Lyapunov function on the first state -/

/-- `V` on the box of the state after the first tick: `ζ = 0`, `|w| ≤ 10⁻⁵`, `|Ev| ≤ 10⁻⁵`,
`|Ea| ≤ 10⁻²`, `|ι| ≤ 10⁻⁴`, `|φ| ≤ 10⁻⁴` give `V ≤ 1/400`. -/
theorem V_first (x : VX) (hζ : |x.ζ| ≤ 0) (hw : |x.w| ≤ 1 / 100000) (hEv : |x.Ev| ≤ 1 / 100000)
    (hEa : |x.Ea| ≤ 1 / 100) (hι : |x.ι| ≤ 1 / 10000) (hφ : |x.φ| ≤ 1 / 10000) :
    V x ≤ 1 / 400 := by
  have t0 := term_le_pos (c := 9200) (by norm_num) hζ hζ
  have t1 := term_le_pos (c := 6600) (by norm_num) hζ hw
  have t2 := term_le_pos (c := 600) (by norm_num) hζ hEv
  have t3 := term_le_pos (c := 42) (by norm_num) hζ hEa
  have t4 := term_le_pos (c := 24000) (by norm_num) hζ hι
  have t5 := term_le_neg (c := (-3200)) (by norm_num) hζ hφ
  have t6 := term_le_pos (c := 3200) (by norm_num) hw hw
  have t7 := term_le_pos (c := 420) (by norm_num) hw hEv
  have t8 := term_le_pos (c := 36) (by norm_num) hw hEa
  have t9 := term_le_neg (c := (-2200)) (by norm_num) hw hι
  have t10 := term_le_neg (c := (-5600)) (by norm_num) hw hφ
  have t11 := term_le_pos (c := 82) (by norm_num) hEv hEv
  have t12 := term_le_pos (c := (27 / 5)) (by norm_num) hEv hEa
  have t13 := term_le_pos (c := 3000) (by norm_num) hEv hι
  have t14 := term_le_neg (c := (-320)) (by norm_num) hEv hφ
  have t15 := term_le_pos (c := (6 / 25)) (by norm_num) hEa hEa
  have t16 := term_le_pos (c := 92) (by norm_num) hEa hι
  have t17 := term_le_neg (c := (-46)) (by norm_num) hEa hφ
  have t18 := term_le_pos (c := 160000) (by norm_num) hι hι
  have t19 := term_le_pos (c := 26000) (by norm_num) hι hφ
  have t20 := term_le_pos (c := 5600) (by norm_num) hφ hφ
  simp only [V]
  norm_num at *
  linarith

/-! ## The first tick -/

set_option maxHeartbeats 4000000 in
/-- **The first tick of the controller's vertical path.** Both vertical PIDs in reset (as
`D_init_controller` leaves them, with the acceleration integrator a zero), the motors' stored
throttle equal to the throttle filter output of value `H = 0.4444`, the plant at the waypoint and
at rest (`ζ = 0`, `w = 0`, specific force `-k H`), the position target within `10⁻⁶` of `-1`, and
the hover sample hypotheses of `vert_tick`: the new throttle filter output has the value `H`, the
exact values of the new floats together with the plant's `ζ' = 0 + h · 0`, `w' = 0 - k h (H - 4/9)`
lie in the sublevel set `V ≤ 1/10`, and the tick invariant `VInv` holds for the new floats. -/
theorem vert_tick0 (hN : NarrowSpec 1)
    -- states at the start of the tick
    (sP : AC_P_1D.State) (sv : AC_PID_Basic.State) (sa : AC_PID.State)
    (m : AP_MotorsMulticopter.State)
    (patt : AC_AttitudeControl_Multi.Params) (satt : AC_AttitudeControl_Multi.State)
    (mi : AP_Motors.Inputs)
    -- the readings
    {tgt zs : Float} {ws fs scZ vff aff cp cr : Float32} (ln lp : Bool)
    -- the PIDs in reset
    (hvr : sv._reset_filter = true)
    (har : sa._flags._reset_filter = true) (haI : Z sa._integrator)
    -- the motors at boot
    (hF : m._throttle_filter_value.IsFinite) (hFv : m._throttle_filter_value.toReal = Hf)
    (hT : m._throttle_in = m._throttle_filter_value)
    (hc : m._throttle_filter_cutoff = AC_PosControl.POSCONTROL_THROTTLE_CUTOFF_FREQ_HZ)
    (hdt : m._dt_s = dtF)
    -- the plant at the waypoint and at rest
    (hzs : Near64 zs (-1) 1e-15) (hws : Z ws) (hfs : Near32 fs (-(k * Hf)) 6e-7)
    -- the hover sample (navigator's stopping point, zero half, C library)
    (htgt : Near64 tgt (-1) 1e-6)
    (hmin : sP._error_min.IsFinite) (hmin' : sP._error_min.toReal ≤ -(1 / 100))
    (hmax : sP._error_max.IsFinite) (hmax' : 1 / 100 ≤ sP._error_max.toReal)
    (hD1 : sP._D1_max.IsFinite) (hD1' : 1 / 100 ≤ sP._D1_max.toReal)
    (hsc : One scZ) (hvff : Z vff) (haff : Z aff)
    (hcp : One cp) (hcr : One cr) (hcos : One (Float32.cos satt._thrust_angle_rad))
    (hhov : mi._throttle_hover = hoverF) :
    let F' := (AP_MotorsMulticopter.update_throttle_filter m)._throttle_filter_value
    let vt := (AC_P_1D.update_all ⟨AC_PosControl.POSCONTROL_D_POS_P⟩ sP tgt zs).2.2 * scZ + vff
    let rv := AC_PID_Basic.update_all pv sv vt ws dtF ln lp
    let atg := rv.2 * scZ + aff
    let ra := AC_PID.update_all pa sa atg (fs + GRAVITY_MSS) dtF false
    let thr := -(ra.2 + AC_PID.get_ff ra.1 - AP_Motors.get_throttle_hover mi)
    let mo := (AC_AttitudeControl_Multi.set_throttle_out patt satt mi cp cr thr true
      AC_PosControl.POSCONTROL_THROTTLE_CUTOFF_FREQ_HZ).2
    F'.toReal = Hf ∧
    V (vx 0 (0 - k * CopterVert.h * (F'.toReal - 4 / 9)) rv.1._error ra.1._error
      ra.1._integrator F') ≤ 1 / 10 ∧
    VInv rv.1 ra.1 { (AP_MotorsMulticopter.update_throttle_filter m) with
      _throttle_in := mo._throttle_in, _throttle_filter_cutoff := mo._throttle_filter_cutoff } := by
  intro F' vt rv atg ra thr mo
  have hu := u32_le; have hu0 := u32_nonneg
  have hIs := Istar_val
  have hIsb : |Istar| ≤ 1 / 20000 := by rw [hIs]; norm_num [abs_le]
  -- motors: the filter keeps its value
  have hφv : m._throttle_filter_value.toReal = 4 / 9 + Istar := by rw [hFv, Istar]; ring
  have hTn : Near32 m._throttle_in (4 / 9 + Istar) 3.7e-8 := by
    rw [hT]; exact (Near32.of_val hF hφv).mono (by norm_num)
  have hTF := throttle_filter_near m hc hdt (Near32.of_val hF hφv) hTn
    (hIsb.trans (by norm_num)) (hIsb.trans (by norm_num))
  have hF'eq : F' = m._throttle_filter_value + (m._throttle_in - m._throttle_filter_value) *
      calc_lowpass_alpha_dt dtF AC_PosControl.POSCONTROL_THROTTLE_CUTOFF_FREQ_HZ := by
    show (AP_MotorsMulticopter.update_throttle_filter m)._throttle_filter_value = _
    rw [hTF.1]
  have hZ0 : Z (m._throttle_in - m._throttle_filter_value) := by
    rw [hT]; exact sub_exact hF hF Z_zero.1 (by rw [sub_self, Z_zero.2])
  have hZ1 := zero_mul_Z near_am.1 hZ0
  have hF'v : F'.IsFinite ∧ F'.toReal = Hf := by
    rw [hF'eq]
    have := add_zero_val hF hZ1
    exact ⟨this.1, this.2.trans hFv⟩
  -- position and velocity
  have hp1 := p1d_near0 hN sP htgt hzs hmin hmin' hmax hmax' hD1 hD1'
  have hvt : Near32 vt 0 1.01e-6 := (hp1.1.mul_one hsc).add_zero hvff
  obtain ⟨v1, v2, v3, v4, v5, v6⟩ := pidv_near0 sv hvr hvt hws ln lp
  have hEvb : |rv.1._error.toReal| ≤ 1.01e-6 := by
    have := v1.bound; rw [abs_zero, zero_add] at this; exact this
  have hat : Near32 atg (kv * rv.1._error.toReal) 1e-12 := (v6.mul_one hsc).add_zero haff
  have hA : |kv * rv.1._error.toReal| ≤ 6e-6 := by
    rw [abs_mul, kv_eq]; norm_num; linarith
  -- acceleration
  have hfs' : Near32 fs (-(k * (Istar + 4 / 9))) 6e-7 := by
    rw [Istar, sub_add_cancel]; exact hfs
  have hmeas := accel_meas_near hfs' (hIsb.trans (by norm_num))
  obtain ⟨a1, a2, a3⟩ := pida_near0 sa har haI hat hA hmeas
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8, -⟩ := pida_eval0 sa hat.1 hmeas.1 har
  have hEab : |(atg - (fs + GRAVITY_MSS)).toReal| ≤ 9.9e-4 := by
    have := a1.bound
    have : |kv * rv.1._error.toReal + k * Istar| ≤ 9.87e-4 := by
      have := abs_le.1 hA
      rw [k_eq, hIs]; apply bnd <;> linarith
    linarith
  have hIb : |(bI sa atg (fs + GRAVITY_MSS)).toReal| ≤ 2.6e-7 := by
    have := a2.bound
    have : |ki * dtc * (atg - (fs + GRAVITY_MSS)).toReal| ≤ 2.5e-7 := by
      rw [abs_mul, abs_mul, abs_of_pos (show (0 : ℝ) < ki by rw [ki_eq]; norm_num),
        abs_of_pos (show (0 : ℝ) < dtc by rw [dtc_eq]; norm_num), ki_eq, dtc_eq]
      nlinarith [abs_nonneg (atg - (fs + GRAVITY_MSS)).toReal]
    linarith
  -- throttle
  have hff : Z (AC_PID.get_ff ra.1) := by
    show Z (ra.1._pid_info.FF + ra.1._pid_info.DFF)
    rw [q7, q8]; exact add_Z (mul_zero_Z hat.1 Z_lit0) (mul_zero_Z Z_lit0.1 Z_lit0)
  have hr : |kp * (atg - (fs + GRAVITY_MSS)).toReal + (bI sa atg (fs + GRAVITY_MSS)).toReal| ≤
      0.0568 := by
    have h1 := abs_le.1 hEab; have h2 := abs_le.1 hIb
    rw [kp_eq]; apply bnd <;> nlinarith
  have hthr_eq : thr = -(ra.2 + AC_PID.get_ff ra.1 - hoverF) := by
    show -(ra.2 + AC_PID.get_ff ra.1 - AP_Motors.get_throttle_hover mi) = _
    rw [throttle_hover_eq mi hhov]
  have hthr : Near32 thr (Hf - (kp * (atg - (fs + GRAVITY_MSS)).toReal +
      (bI sa atg (fs + GRAVITY_MSS)).toReal)) 3.7e-8 := by
    rw [hthr_eq]; exact throttle_near a3 hr hff
  obtain ⟨s1, s2, s3⟩ := set_throttle_out_val patt satt mi
    (c := AC_PosControl.POSCONTROL_THROTTLE_CUTOFF_FREQ_HZ) hcp hcr hcos hthr.1
  have hmo : Near32 mo._throttle_in (4 / 9 + (-(kp * ra.1._error.toReal) -
      (ra.1._integrator.toReal - Istar))) 3.7e-8 := by
    refine Near32.of_eq_val s1 s2 (hthr.congr ?_)
    rw [q2, q5, Istar]; ring
  refine ⟨hF'v.2, ?_, ?_⟩
  · -- the Lyapunov function
    rw [hF'v.2]
    apply le_trans (V_first _ ?_ ?_ ?_ ?_ ?_ ?_) (by norm_num)
    · show |(0 : ℝ)| ≤ 0
      simp
    · show |0 - k * CopterVert.h * (Hf - 4 / 9)| ≤ _
      rw [show Hf - 4 / 9 = Istar from rfl, hIs, k_eq, h_eq]; norm_num [abs_le]
    · show |rv.1._error.toReal| ≤ _
      linarith
    · show |ra.1._error.toReal| ≤ _
      rw [q2]; linarith
    · show |ra.1._integrator.toReal - Istar| ≤ _
      rw [q5]
      have := abs_le.1 hIb
      rw [hIs]; apply bnd <;> linarith
    · show |F'.toReal - 4 / 9| ≤ _
      rw [hF'v.2, show Hf - 4 / 9 = Istar from rfl, hIs]; norm_num [abs_le]
  · -- the invariant
    refine ⟨v3, v1.1, v4, v5, q6, ?_, ?_, ?_, ?_, ?_, ?_, hF'v.1, s3, hmo⟩
    · rw [q1]; exact hat.1
    · rw [q1]
      have := hat.bound
      linarith [abs_nonneg (kv * rv.1._error.toReal)]
    · rw [q2]; exact a1.1
    · rw [q5]; exact a2.1
    · rw [q3]; exact Z_lit0.1
    · rw [q3, Z_lit0.2]; norm_num

end

end Contracts.CopterHover
