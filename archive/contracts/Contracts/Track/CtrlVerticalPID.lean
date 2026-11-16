import Contracts.Track.CtrlVerticalFloat

/-!
# C5, C6: the vertical position P, velocity PI and acceleration PID

The three controllers `D_update_controller` calls, each on the parameter values of the parameter
file and inside the region, as the real law of `VERTICAL.md` plus an explicit `β`
(statements in `CTRL_VERTICAL.md`):

* `accel_pid` (C6, `AC_PID::update_all`): the target filter (`FLTT = 0`) passes the target, the error
  filter is the 20 Hz step with `αA`, the integrator adds `kiDt e⁺` (clamp inactive), the output is
  `kpAcc e⁺ + I⁺`, and `get_ff` is `0`;
* `pos_p` (C5, `AC_P_1D::update_all`): `(float)(target - pos)`, the sqrt controller in its linear
  zone, the error limits inactive;
* `vel_pi` (C5, `AC_PID_Basic::update_all`): the 5 Hz step with `αV`, output `5 e⁺`, integrator `0`.

`accel_pid2`, `vel_pi2` are the sharp forms the tick uses: the coefficients exact under the float
fact `PiF32`, and the `β`s in terms of the error magnitudes (`|target - meas|`, the filter state)
instead of the signal magnitudes.
-/

namespace Contracts.Track.CtrlV

open Float.Model UnpackedFloat Contracts.Mission

noncomputable section

set_option linter.unusedSimpArgs false

/-! ## `AC_PID` (the vertical acceleration controller) -/

section PID
open AC_PosControl_lib

set_option maxHeartbeats 1000000 in
set_option linter.unusedSimpArgs false in
/-- `SlewLimiter::modifier` returns `1` when `slew_rate_max ≤ 0` (`SMAX = 0`): the slew limiter is
inert. -/
theorem modifier_snd (s : SlewLimiter.State) (srm tau : Float32) inp (sample dt : Float32)
    (h : srm ≤ Int32.toFloat32 (0 : Int32)) :
    (SlewLimiter.modifier s ⟨srm, tau⟩ inp sample dt).2 = Float.toFloat32 (1.0 : Float) := by
  unfold SlewLimiter.modifier
  split
  · rfl
  · dsimp only
    split <;> split <;> (try split) <;> (try split) <;> simp [h]

/-! The fields of `AC_PID::update_all` on its nominal branches (one lemma per field: the
conjunction elaborates too slowly). -/

/-- Unfolds `AC_PID::update_all` along the nominal branches. -/
macro "pid_unfold" : tactic => `(tactic| (
  unfold AC_PID.update_all
  simp only [Bool.not_true, Bool.or_false, Bool.false_eq_true, ite_false, ite_true, *]
  unfold AC_PID.update_i
  simp only [Bool.not_false, Bool.true_and, ite_true, Bool.true_or, Bool.false_eq_true, ite_false, *]))

theorem pid_T (p : AC_PID.Params) (s : AC_PID.State) (inp : AC_PID.Inputs)
    (target meas dt : Float32) (ht : target.IsFinite) (hm : meas.IsFinite)
    (hr : s._flags._reset_filter = false) (hdtp : is_positive_float dt = true)
    (hki : is_zero_AP_Float p._ki = false) (hpd : is_positive_AP_Float p._kpdmax = false) :
    let r := AC_PID.update_all p s inp target meas dt false 1.0 1.0
    r.1._target = s._target + AC_PID.get_filt_T_alpha p dt * (target - s._target) := by
  have ht' : Float32.isFinite target = true := ht
  have hm' : Float32.isFinite meas = true := hm
  pid_unfold
  rfl

theorem pid_E (p : AC_PID.Params) (s : AC_PID.State) (inp : AC_PID.Inputs)
    (target meas dt : Float32) (ht : target.IsFinite) (hm : meas.IsFinite)
    (hr : s._flags._reset_filter = false) (hdtp : is_positive_float dt = true)
    (hki : is_zero_AP_Float p._ki = false) (hpd : is_positive_AP_Float p._kpdmax = false) :
    let r := AC_PID.update_all p s inp target meas dt false 1.0 1.0
    r.1._error = s._error + AC_PID.get_filt_E_alpha p dt * (r.1._target - meas - s._error) := by
  have ht' : Float32.isFinite target = true := ht
  have hm' : Float32.isFinite meas = true := hm
  pid_unfold
  rfl

theorem pid_I (p : AC_PID.Params) (s : AC_PID.State) (inp : AC_PID.Inputs)
    (target meas dt : Float32) (ht : target.IsFinite) (hm : meas.IsFinite)
    (hr : s._flags._reset_filter = false) (hdtp : is_positive_float dt = true)
    (hki : is_zero_AP_Float p._ki = false) (hpd : is_positive_AP_Float p._kpdmax = false) :
    let r := AC_PID.update_all p s inp target meas dt false 1.0 1.0
    r.1._integrator = constrain_value_line_float (s._integrator + r.1._error * p._ki * 1.0 * dt)
      (-p._kimax) p._kimax (Int32.toUInt32 346) := by
  have ht' : Float32.isFinite target = true := ht
  have hm' : Float32.isFinite meas = true := hm
  pid_unfold
  rfl

theorem pid_D (p : AC_PID.Params) (s : AC_PID.State) (inp : AC_PID.Inputs)
    (target meas dt : Float32) (ht : target.IsFinite) (hm : meas.IsFinite)
    (hr : s._flags._reset_filter = false) (hdtp : is_positive_float dt = true)
    (hki : is_zero_AP_Float p._ki = false) (hpd : is_positive_AP_Float p._kpdmax = false) :
    let r := AC_PID.update_all p s inp target meas dt false 1.0 1.0
    r.1._derivative = s._derivative + AC_PID.get_filt_D_alpha p dt * ((r.1._error - s._error) / dt - s._derivative) := by
  have ht' : Float32.isFinite target = true := ht
  have hm' : Float32.isFinite meas = true := hm
  pid_unfold
  rfl

theorem pid_Td (p : AC_PID.Params) (s : AC_PID.State) (inp : AC_PID.Inputs)
    (target meas dt : Float32) (ht : target.IsFinite) (hm : meas.IsFinite)
    (hr : s._flags._reset_filter = false) (hdtp : is_positive_float dt = true)
    (hki : is_zero_AP_Float p._ki = false) (hpd : is_positive_AP_Float p._kpdmax = false) :
    let r := AC_PID.update_all p s inp target meas dt false 1.0 1.0
    r.1._target_derivative = (r.1._target - s._target) / dt := by
  have ht' : Float32.isFinite target = true := ht
  have hm' : Float32.isFinite meas = true := hm
  pid_unfold
  rfl

theorem pid_R (p : AC_PID.Params) (s : AC_PID.State) (inp : AC_PID.Inputs)
    (target meas dt : Float32) (ht : target.IsFinite) (hm : meas.IsFinite)
    (hr : s._flags._reset_filter = false) (hdtp : is_positive_float dt = true)
    (hki : is_zero_AP_Float p._ki = false) (hpd : is_positive_AP_Float p._kpdmax = false) :
    let r := AC_PID.update_all p s inp target meas dt false 1.0 1.0
    r.1._flags._reset_filter = false := by
  have ht' : Float32.isFinite target = true := ht
  have hm' : Float32.isFinite meas = true := hm
  pid_unfold
  exact hr

theorem pid_FF (p : AC_PID.Params) (s : AC_PID.State) (inp : AC_PID.Inputs)
    (target meas dt : Float32) (ht : target.IsFinite) (hm : meas.IsFinite)
    (hr : s._flags._reset_filter = false) (hdtp : is_positive_float dt = true)
    (hki : is_zero_AP_Float p._ki = false) (hpd : is_positive_AP_Float p._kpdmax = false) :
    let r := AC_PID.update_all p s inp target meas dt false 1.0 1.0
    r.1._pid_info.FF = r.1._target * p._kff := by
  have ht' : Float32.isFinite target = true := ht
  have hm' : Float32.isFinite meas = true := hm
  pid_unfold
  rfl

theorem pid_DFF (p : AC_PID.Params) (s : AC_PID.State) (inp : AC_PID.Inputs)
    (target meas dt : Float32) (ht : target.IsFinite) (hm : meas.IsFinite)
    (hr : s._flags._reset_filter = false) (hdtp : is_positive_float dt = true)
    (hki : is_zero_AP_Float p._ki = false) (hpd : is_positive_AP_Float p._kpdmax = false) :
    let r := AC_PID.update_all p s inp target meas dt false 1.0 1.0
    r.1._pid_info.DFF = r.1._target_derivative * p._kdff := by
  have ht' : Float32.isFinite target = true := ht
  have hm' : Float32.isFinite meas = true := hm
  pid_unfold
  rfl

theorem pid_O (p : AC_PID.Params) (s : AC_PID.State) (inp : AC_PID.Inputs)
    (target meas dt : Float32) (ht : target.IsFinite) (hm : meas.IsFinite)
    (hr : s._flags._reset_filter = false) (hdtp : is_positive_float dt = true)
    (hki : is_zero_AP_Float p._ki = false) (hpd : is_positive_AP_Float p._kpdmax = false) :
    let r := AC_PID.update_all p s inp target meas dt false 1.0 1.0
    r.2 = r.1._error * p._kp * r.1._pid_info.Dmod * 1.0 +
      r.1._derivative * p._kd * r.1._pid_info.Dmod * 1.0 + r.1._integrator := by
  have ht' : Float32.isFinite target = true := ht
  have hm' : Float32.isFinite meas = true := hm
  pid_unfold
  rfl

theorem pid_X (p : AC_PID.Params) (s : AC_PID.State) (inp : AC_PID.Inputs)
    (target meas dt : Float32) (ht : target.IsFinite) (hm : meas.IsFinite)
    (hr : s._flags._reset_filter = false) (hdtp : is_positive_float dt = true)
    (hki : is_zero_AP_Float p._ki = false) (hpd : is_positive_AP_Float p._kpdmax = false) :
    let r := AC_PID.update_all p s inp target meas dt false 1.0 1.0
    ∃ X Y, r.1._pid_info.Dmod = (SlewLimiter.modifier X ⟨p._slew_rate_max, p._slew_rate_tau⟩
      inp._slew_limiter Y dt).2 := by
  have ht' : Float32.isFinite target = true := ht
  have hm' : Float32.isFinite meas = true := hm
  pid_unfold
  exact ⟨_, _, rfl⟩


/-- `PSC_D_ACC_P = 0.05f` and `PSC_D_ACC_I = 0.1f` as reals. -/
def kpA : ℝ := 13421773 / 268435456
def kiA : ℝ := 13421773 / 134217728

theorem kiA_dtR : kiA * dtR = ((Contracts.Track.Vertical.kiDt : ℚ) : ℝ) := by
  rw [kiA, dtR, Contracts.Track.Vertical.kiDt]; push_cast; norm_num

theorem kpA_eq : kpA = ((Contracts.Track.Vertical.kpAcc : ℚ) : ℝ) := by
  rw [kpA, Contracts.Track.Vertical.kpAcc]; push_cast; norm_num

theorem αA_eq : ((16042859 / 67108864 : ℚ) : ℝ) = ((Contracts.Track.Vertical.αA : ℚ) : ℝ) := by
  rw [Contracts.Track.Vertical.αA]

/-- The integrator step of `AC_PID::update_i`, `constrain(I + e ki · 1 · dt, -IMAX, IMAX)`, with
`ki = 0.1f`, `dt = 0.0025f`, `|e| ≤ 3M` and the clamp inactive (`|I| + M/2¹⁰ ≤ IMAX`). -/
theorem integ_step {I e ki dt k : Float32} {M : ℝ} (hI : I.IsFinite) (he : e.IsFinite)
    (hki : ki.IsFinite) (hkiv : ki.toReal = kiA) (hdt : dt.IsFinite) (hdtv : dt.toReal = dtR)
    (hk : k.IsFinite) (hk' : k.toReal ≤ 2 ^ 10) (hM1 : 1 ≤ M) (hM : M ≤ 2 ^ 10)
    (heM : |e.toReal| ≤ 3 * M) (himax : |I.toReal| + M / 2 ^ 10 ≤ k.toReal) (l : UInt32) :
    A32 (constrain_value_line_float (I + e * ki * 1.0 * dt) (-k) k l)
      (I.toReal + kiA * dtR * e.toReal) (u32 * |I.toReal| + u32 * M / 2 ^ 7 + 4 * η32) ∧
    |(constrain_value_line_float (I + e * ki * 1.0 * dt) (-k) k l).toReal| ≤ k.toReal := by
  have hη1 := η32_small; have hη0 := η32_pos
  have hu : u32 = 1 / 16777216 := u32_eq
  have hki' : A32 ki kiA 0 := (A32.of_exact hki).congr hkiv
  have hdt' : A32 dt dtR 0 := (A32.of_exact hdt).congr hdtv
  have hea := abs_nonneg e.toReal
  have hEk : |e.toReal * kiA| ≤ 3 * M / 2 ^ 3 := by
    rw [abs_mul, kiA]; norm_num; nlinarith
  have i1 := (A32.of_exact he).mul hki' (by
    simp only [mul_zero, zero_mul, add_zero, abs_zero]; have := hEk; norm_num [capF] at this ⊢; linarith)
  obtain ⟨i2f, i2v⟩ := f32_mul_one i1.1 Float32.isFinite_lit_one Float32.toReal_lit_one
  have i2 : A32 (e * ki * 1.0) (e.toReal * kiA) (u32 * (3 * M / 2 ^ 3) + η32) := ⟨i2f, by
    rw [i2v]; have := i1.2; simp only [mul_zero, zero_mul, add_zero, abs_zero, zero_add] at this
    have h2 : u32 * |e.toReal * kiA| ≤ u32 * (3 * M / 2 ^ 3) := mul_le_mul_of_nonneg_left hEk u32_pos.le
    exact this.trans (by linarith)⟩
  have hEkd : |e.toReal * kiA * dtR| ≤ M / 1300 := by
    rw [abs_mul, abs_mul, kiA, dtR]; norm_num; nlinarith
  have i3 := i2.mul hdt' (by
    simp only [mul_zero, zero_mul, add_zero, abs_zero]
    rw [abs_of_pos (by rw [dtR]; norm_num : (0 : ℝ) < dtR)]
    have := hEk; rw [hu, dtR]; norm_num [capF] at this ⊢; nlinarith)
  have i3' : A32 (e * ki * 1.0 * dt) (e.toReal * kiA * dtR) (u32 * M / 2 ^ 8 + 2 * η32) := by
    refine i3.mono ?_
    simp only [mul_zero, zero_mul, add_zero, abs_zero, zero_add]
    rw [abs_of_pos (by rw [dtR]; norm_num : (0 : ℝ) < dtR)]
    have := hEk; rw [hu, dtR]; norm_num at this ⊢; nlinarith
  have hIa := abs_nonneg I.toReal
  have hadd := abs_add_le I.toReal (e.toReal * kiA * dtR)
  have i4 := (A32.of_exact hI).add i3' (by
    simp only [add_zero, zero_add]; rw [hu] at *; norm_num [capF]; nlinarith)
  have i4' : A32 (I + e * ki * 1.0 * dt) (I.toReal + kiA * dtR * e.toReal)
      (u32 * |I.toReal| + u32 * M / 2 ^ 7 + 4 * η32) := by
    refine (i4.mono ?_).congr (by ring)
    simp only [zero_add]
    rw [hu] at *; nlinarith
  have hcl : |(I + e * ki * 1.0 * dt).toReal| ≤ k.toReal := by
    have h1 := i4'.abs_le
    have h2 : |I.toReal + kiA * dtR * e.toReal| ≤ |I.toReal| + M / 1300 := by
      rw [show kiA * dtR * e.toReal = e.toReal * kiA * dtR by ring]; linarith
    have hI10 : |I.toReal| ≤ 2 ^ 10 := by linarith
    rw [hu] at h1; norm_num at h1 h2 himax hI10 ⊢; linarith
  obtain ⟨fc, ec⟩ := constrain_spec l i4'.1 ((Float32.isFinite_neg _).2 hk) hk
    (by rw [Float32.toReal_neg]; linarith)
  rw [Float32.toReal_neg] at ec
  have hcl' := abs_le.1 hcl
  rw [min_eq_right hcl'.2, max_eq_right hcl'.1] at ec
  exact ⟨⟨fc, by rw [ec]; exact i4'.2⟩, by rw [ec]; exact hcl⟩

/-- The output of `AC_PID::update_all` with `Dmod = 1`, `pd_scale = 1`, `kd = 0`:
`(e kp Dmod) 1 + (D kd Dmod) 1 + I = kp e + I` up to two roundings. -/
theorem pd_out {e kp Dm D kd I : Float32} {M K : ℝ} (he : e.IsFinite) (hkp : kp.IsFinite)
    (hkpv : kp.toReal = kpA) (hDm : Dm.IsFinite) (hDmv : Dm.toReal = 1) (hD : D.IsFinite)
    (hkd : kd.IsFinite) (hkdv : kd.toReal = 0) (hI : I.IsFinite) (hM1 : 1 ≤ M) (hM : M ≤ 2 ^ 10)
    (heM : |e.toReal| ≤ 3 * M) (hIK : |I.toReal| ≤ K) (hK : K ≤ 2 ^ 10) :
    A32 (e * kp * Dm * 1.0 + D * kd * Dm * 1.0 + I) (kpA * e.toReal + I.toReal)
      (u32 * (M / 2 + K) + 4 * η32) := by
  have hη1 := η32_small; have hη0 := η32_pos
  have hu : u32 = 1 / 16777216 := u32_eq
  have hek : |e.toReal * kpA| ≤ 3 * M / 2 ^ 4 := by
    rw [abs_mul, kpA]; norm_num; nlinarith [abs_nonneg e.toReal]
  have p1 := (A32.of_exact he).mul ((A32.of_exact hkp).congr hkpv) (by
    simp only [mul_zero, zero_mul, add_zero, abs_zero]; have := hek; norm_num [capF] at this ⊢; linarith)
  simp only [mul_zero, zero_mul, add_zero, abs_zero, zero_add] at p1
  obtain ⟨p2f, p2v⟩ := f32_mul_one p1.1 hDm hDmv
  obtain ⟨p3f, p3v⟩ := f32_mul_one p2f Float32.isFinite_lit_one Float32.toReal_lit_one
  obtain ⟨q1f, q1v⟩ := f32_mul_zero hD hkd hkdv
  obtain ⟨q2f, q2v⟩ := f32_mul_exact q1f hDm Float32.isFinite_lit_zero (by
    rw [q1v, zero_mul, Float32.toReal_lit_zero])
  rw [Float32.toReal_lit_zero] at q2v
  obtain ⟨q3f, q3v⟩ := f32_mul_exact q2f Float32.isFinite_lit_one Float32.isFinite_lit_zero (by
      rw [q2v, zero_mul, Float32.toReal_lit_zero])
  rw [Float32.toReal_lit_zero] at q3v
  obtain ⟨s1f, s1v⟩ := f32_add_zero p3f q3f q3v
  have s1 : A32 (e * kp * Dm * 1.0 + D * kd * Dm * 1.0) (e.toReal * kpA)
      (u32 * |e.toReal * kpA| + η32) := ⟨s1f, by rw [s1v, p3v, p2v]; exact p1.2⟩
  have hadd := abs_add_le (e.toReal * kpA) I.toReal
  have s2 := s1.add (A32.of_exact hI) (by
    simp only [add_zero]; have := hek; rw [hu]; norm_num [capF] at this ⊢; nlinarith)
  refine (s2.mono ?_).congr (by ring)
  simp only [add_zero]
  rw [hu] at *; nlinarith [abs_nonneg (e.toReal * kpA)]

set_option maxHeartbeats 4000000 in
/-- **C6, `AC_PID::update_all` as `D_update_controller` calls it** (vertical acceleration,
`limit = false` inside the region, `pd_scale = i_scale = 1`). Parameters of the parameter file:
`PSC_D_ACC_P 0.05`, `I 0.1`, `D = FF = D_FF = 0`, `FLTT = 0`, `FLTE = 20`, `FLTD = 0`,
`SMAX = PDMX = 0`. On finite inputs and state of magnitude at most `M` (the error filter `2M`),
with the integrator `M/2¹⁰` inside `IMAX`:

* the target filter (`FLTT = 0`) passes the target: `⟦T⁺⟧ = target + βT`;
* the error filter: `⟦eA⁺⟧ = eA + αA ((target - meas) - eA) + βE`;
* the integrator (clamp inactive): `⟦I⁺⟧ = I + kiDt ⟦eA⁺⟧ + βI`;
* the output: `kpAcc ⟦eA⁺⟧ + ⟦I⁺⟧ + βO`; the feedforward `get_ff` is exactly `0`;
* the reset flag stays clear and the derivative filter stays finite and below `2³⁰`. -/
theorem accel_pid (hL : LibmSpec) (p : AC_PID.Params) (s : AC_PID.State) (inp : AC_PID.Inputs)
    (target meas dt : Float32) {M : ℝ}
    (hkp : p._kp.IsFinite) (hkpv : p._kp.toReal = kpA)
    (hki : p._ki.IsFinite) (hkiv : p._ki.toReal = kiA)
    (hkd : p._kd.IsFinite) (hkdv : p._kd.toReal = 0)
    (hkff : p._kff.IsFinite) (hkffv : p._kff.toReal = 0)
    (hkdff : p._kdff.IsFinite) (hkdffv : p._kdff.toReal = 0)
    (hpd : p._kpdmax.IsFinite) (hpdv : p._kpdmax.toReal = 0)
    (hsr : p._slew_rate_max.IsFinite) (hsrv : p._slew_rate_max.toReal = 0)
    (hfT : p._filt_T_hz.IsFinite) (hfTv : p._filt_T_hz.toReal = 0)
    (hfE : p._filt_E_hz.IsFinite) (hfEv : p._filt_E_hz.toReal = 20)
    (hfD : p._filt_D_hz.IsFinite) (hfDv : p._filt_D_hz.toReal = 0)
    (himx : p._kimax.IsFinite) (himx' : p._kimax.toReal ≤ 2 ^ 10)
    (hdt : dt.IsFinite) (hdtv : dt.toReal = dtR)
    (hr : s._flags._reset_filter = false)
    (hT : s._target.IsFinite) (hE : s._error.IsFinite) (hI : s._integrator.IsFinite)
    (hD : s._derivative.IsFinite) (ht : target.IsFinite) (hm : meas.IsFinite)
    (hM1 : 1 ≤ M) (hM : M ≤ 2 ^ 10)
    (hTM : |s._target.toReal| ≤ M) (htM : |target.toReal| ≤ M) (hmM : |meas.toReal| ≤ M)
    (hEM : |s._error.toReal| ≤ 2 * M) (hDM : |s._derivative.toReal| ≤ 2 ^ 30)
    (himax : |s._integrator.toReal| + M / 2 ^ 10 ≤ p._kimax.toReal) :
    let r := AC_PID.update_all p s inp target meas dt false 1.0 1.0
    A32 r.1._target target.toReal (13 * u32 * M + 2 * η32) ∧
    A32 r.1._error (s._error.toReal + (16042859 / 67108864 : ℝ) *
        ((target.toReal - meas.toReal) - s._error.toReal)) (44 * u32 * M + 4 * η32) ∧
    A32 r.1._integrator (s._integrator.toReal + kiA * dtR * r.1._error.toReal)
        (u32 * |s._integrator.toReal| + u32 * M / 2 ^ 7 + 4 * η32) ∧
    A32 r.2 (kpA * r.1._error.toReal + r.1._integrator.toReal)
        (u32 * (M / 2 + p._kimax.toReal) + 4 * η32) ∧
    (AC_PID.get_ff r.1).IsFinite ∧ (AC_PID.get_ff r.1).toReal = 0 ∧
    r.1._flags._reset_filter = false ∧ r.1._derivative.IsFinite ∧
    |r.1._derivative.toReal| ≤ 2 ^ 30 ∧ |r.1._error.toReal| ≤ 3 * M := by
  intro r
  have hη1 := η32_small; have hη0 := η32_pos
  have hu : u32 = 1 / 16777216 := u32_eq
  have hM0 : (0 : ℝ) ≤ M := by linarith
  -- the branch conditions
  have hdtp : is_positive_float dt = true := by rw [isPos_iff hdt, hdtv, dtR]; norm_num
  have hkiz : is_zero_AP_Float p._ki = false := by
    show is_zero_float p._ki = false
    rw [Bool.eq_false_iff, ne_eq, isZero_iff hki, hkiv, kiA]; norm_num
  have hsr' : p._slew_rate_max ≤ Int32.toFloat32 (0 : Int32) := by
    rw [Float32.le_iff_toReal_le hsr Float32.isFinite_int32_zero, hsrv, Float32.toReal_int32_zero]
  have hpd' : is_positive_AP_Float p._kpdmax = false := by
    rw [Bool.eq_false_iff, ne_eq, isPosAP_iff hpd, hpdv]; norm_num
  have eT := pid_T p s inp target meas dt ht hm hr hdtp hkiz hpd'
  have eE := pid_E p s inp target meas dt ht hm hr hdtp hkiz hpd'
  have eI := pid_I p s inp target meas dt ht hm hr hdtp hkiz hpd'
  have eD := pid_D p s inp target meas dt ht hm hr hdtp hkiz hpd'
  have eTd := pid_Td p s inp target meas dt ht hm hr hdtp hkiz hpd'
  have eR := pid_R p s inp target meas dt ht hm hr hdtp hkiz hpd'
  have eFF := pid_FF p s inp target meas dt ht hm hr hdtp hkiz hpd'
  have eDFF := pid_DFF p s inp target meas dt ht hm hr hdtp hkiz hpd'
  have eO := pid_O p s inp target meas dt ht hm hr hdtp hkiz hpd'
  obtain ⟨X, Y, eDm⟩ := pid_X p s inp target meas dt ht hm hr hdtp hkiz hpd'
  have hDm : r.1._pid_info.Dmod.IsFinite ∧ r.1._pid_info.Dmod.toReal = 1 := by
    rw [eDm, modifier_snd _ _ _ _ _ _ hsr']; exact f32_ofF64_one hL
  -- the coefficients
  have aT : A32 (AC_PID.get_filt_T_alpha p dt) 1 0 :=
    alpha0 hL hdt (by rw [hdtv, dtR]; norm_num) hfT hfTv
  have aE : A32 (AC_PID.get_filt_E_alpha p dt) (16042859 / 67108864) (1 / 2 ^ 22) :=
    alpha20 hL hdt hdtv hfE hfEv
  have aD : A32 (AC_PID.get_filt_D_alpha p dt) 1 0 :=
    alpha0 hL hdt (by rw [hdtv, dtR]; norm_num) hfD hfDv
  -- the target filter
  have hT' : A32 r.1._target target.toReal (13 * u32 * M + 2 * η32) := by
    rw [eT]
    have := A32.filt hT (A32.of_exact ht) aT (by norm_num) le_rfl (by norm_num) hM0 htM hTM
      (by linarith)
    simp only [mul_zero, zero_add, one_mul, add_sub_cancel] at this
    refine this.mono (le_of_eq ?_); ring
  -- the error
  have herr := hT'.sub (A32.of_exact hm) (by
    rw [hu]; have := abs_sub target.toReal meas.toReal; norm_num [capF]; nlinarith)
  have herr' : A32 (r.1._target - meas) (target.toReal - meas.toReal) (16 * u32 * M + 4 * η32) := by
    refine herr.mono ?_
    have := abs_sub target.toReal meas.toReal
    rw [hu] at *; nlinarith
  have hE' : A32 r.1._error (s._error.toReal + (16042859 / 67108864 : ℝ) *
      ((target.toReal - meas.toReal) - s._error.toReal)) (44 * u32 * M + 4 * η32) := by
    rw [eE]
    have := A32.filt (M := 2 * M) hE herr' aE (by norm_num) (by norm_num) (by norm_num)
      (by rw [hu]; nlinarith) ((abs_sub _ _).trans (by linarith)) hEM (by linarith)
    refine this.mono ?_
    rw [hu]; nlinarith
  have hE'b : |r.1._error.toReal| ≤ 3 * M := by
    have h1 := hE'.abs_le
    have h2 : |s._error.toReal + (16042859 / 67108864 : ℝ) * ((target.toReal - meas.toReal) - s._error.toReal)| ≤ 2 * M := by
      have : s._error.toReal + (16042859 / 67108864 : ℝ) * ((target.toReal - meas.toReal) - s._error.toReal) =
          (1 - 16042859 / 67108864) * s._error.toReal + (16042859 / 67108864) * (target.toReal - meas.toReal) := by ring
      rw [this]
      have := abs_add_le ((1 - 16042859 / 67108864 : ℝ) * s._error.toReal) ((16042859 / 67108864 : ℝ) * (target.toReal - meas.toReal))
      rw [abs_mul, abs_mul] at this
      have := abs_sub target.toReal meas.toReal
      norm_num at *
      nlinarith
    rw [hu] at h1; nlinarith
  -- the integrator
  obtain ⟨hI', hIk⟩ := integ_step (l := Int32.toUInt32 346) hI hE'.1 hki hkiv hdt hdtv himx himx'
    hM1 hM hE'b himax
  rw [← eI] at hI' hIk
  -- the derivative filter
  have hE5 : |r.1._error.toReal - s._error.toReal| ≤ 5 * M := (abs_sub _ _).trans (by linarith)
  have hdE := (A32.of_exact hE'.1).sub (A32.of_exact hE) (by
    simp only [add_zero]; norm_num [capF]; linarith)
  simp only [add_zero] at hdE
  have hdE' : A32 (r.1._error - s._error) (r.1._error.toReal - s._error.toReal) 1 :=
    hdE.mono (by rw [hu]; nlinarith)
  have hq := hdE'.div ((A32.of_exact hdt).congr hdtv) (m := 1 / 401) (by norm_num)
    (by rw [dtR]; norm_num) (by
      rw [abs_div, abs_of_pos (by rw [dtR]; norm_num : (0 : ℝ) < dtR), dtR]
      norm_num [capF]; nlinarith)
  have hq' : A32 ((r.1._error - s._error) / dt) ((r.1._error.toReal - s._error.toReal) / dtR) (2 ^ 20) :=
    hq.mono (by
      rw [abs_div, abs_of_pos (by rw [dtR]; norm_num : (0 : ℝ) < dtR), dtR, hu]
      norm_num; nlinarith)
  have hqb : |(r.1._error.toReal - s._error.toReal) / dtR| ≤ 2 ^ 22 := by
    rw [abs_div, abs_of_pos (by rw [dtR]; norm_num : (0 : ℝ) < dtR), dtR, div_le_iff₀ (by norm_num)]
    norm_num; linarith
  have hD' := A32.filt (M := 2 ^ 30) hD hq' aD (by norm_num) le_rfl (by norm_num) (by norm_num)
    (by linarith) hDM (by norm_num)
  rw [← eD] at hD'
  have hD'b : |r.1._derivative.toReal| ≤ 2 ^ 30 := by
    have := hD'.abs_le
    simp only [one_mul, add_sub_cancel, mul_zero, zero_add] at this
    rw [hu] at this; norm_num at this; linarith
  -- the output
  have hO := pd_out hE'.1 hkp hkpv hDm.1 hDm.2 hD'.1 hkd hkdv hI'.1 hM1 hM hE'b hIk himx'
  rw [← eO] at hO
  -- the feedforward
  have hTd : r.1._target_derivative.IsFinite := by
    rw [eTd]
    have h1 := hT'.sub (A32.of_exact hT) (by
      simp only [add_zero]; rw [hu]; norm_num [capF]; have := abs_sub target.toReal s._target.toReal; nlinarith)
    have h2 := h1.div ((A32.of_exact hdt).congr hdtv) (m := 1 / 401) (by norm_num)
      (by rw [dtR]; norm_num) (by
        rw [abs_div, abs_of_pos (by rw [dtR]; norm_num : (0 : ℝ) < dtR), dtR]
        have := abs_sub target.toReal s._target.toReal
        rw [hu]; norm_num [capF]; nlinarith)
    exact h2.1
  obtain ⟨fF, vF⟩ := f32_mul_zero hT'.1 hkff hkffv
  obtain ⟨fDF, vDF⟩ := f32_mul_zero hTd hkdff hkdffv
  rw [← eFF] at fF vF
  rw [← eDFF] at fDF vDF
  obtain ⟨fff, vff⟩ := f32_add_exact fF fDF Float32.isFinite_lit_zero (by
    rw [vF, vDF, Float32.toReal_lit_zero, add_zero])
  rw [Float32.toReal_lit_zero] at vff
  exact ⟨hT', hE', hI', hO, fff, vff, eR, hD'.1, hD'b, hE'b⟩

end PID


section Basic
open AC_PosControl_lib

/-! ## `AC_PID_Basic::update_all` (the vertical velocity PI), field by field -/

/-- Unfolds `AC_PID_Basic::update_all` along the nominal branches. -/
macro "basic_unfold" : tactic => `(tactic| (
  unfold AC_PID_Basic.update_all_float3_bool2
  simp only [Bool.not_true, Bool.or_false, Bool.false_or, Bool.false_eq_true, ite_false, ite_true,
    Bool.not_false, *]
  unfold AC_PID_Basic.update_i
  simp only [Bool.not_false, Bool.true_and, ite_true, Bool.true_or, Bool.false_eq_true, ite_false,
    Bool.not_true, *]))

theorem basic_T (p : AC_PID_Basic.Params) (s : AC_PID_Basic.State) (target meas dt : Float32)
    (ln lp : Bool) (ht : target.IsFinite) (hm : meas.IsFinite) (hr : s._reset_filter = false)
    (hdtp : is_positive_float dt = true) (hki : is_zero_AP_Float p._ki = true) :
    (AC_PID_Basic.update_all_float3_bool2 p s target meas dt ln lp).1._target = target := by
  have ht' : Float32.isFinite target = true := ht
  have hm' : Float32.isFinite meas = true := hm
  have ht'' : Float32.isNaN target = false := Float32.not_isNaN_of_isFinite ht
  have hm'' : Float32.isNaN meas = false := Float32.not_isNaN_of_isFinite hm
  basic_unfold
  rfl

theorem basic_E (p : AC_PID_Basic.Params) (s : AC_PID_Basic.State) (target meas dt : Float32)
    (ln lp : Bool) (ht : target.IsFinite) (hm : meas.IsFinite) (hr : s._reset_filter = false)
    (hdtp : is_positive_float dt = true) (hki : is_zero_AP_Float p._ki = true) :
    (AC_PID_Basic.update_all_float3_bool2 p s target meas dt ln lp).1._error =
      s._error + AC_PID_Basic.get_filt_E_alpha p dt * (target - meas - s._error) := by
  have ht' : Float32.isFinite target = true := ht
  have hm' : Float32.isFinite meas = true := hm
  have ht'' : Float32.isNaN target = false := Float32.not_isNaN_of_isFinite ht
  have hm'' : Float32.isNaN meas = false := Float32.not_isNaN_of_isFinite hm
  basic_unfold
  rfl


theorem basic_D (p : AC_PID_Basic.Params) (s : AC_PID_Basic.State) (target meas dt : Float32)
    (ln lp : Bool) (ht : target.IsFinite) (hm : meas.IsFinite) (hr : s._reset_filter = false)
    (hdtp : is_positive_float dt = true) (hki : is_zero_AP_Float p._ki = true) :
    let r := AC_PID_Basic.update_all_float3_bool2 p s target meas dt ln lp
    r.1._derivative = s._derivative + AC_PID_Basic.get_filt_D_alpha p dt *
      ((r.1._error - s._error) / dt - s._derivative) := by
  have ht' : Float32.isFinite target = true := ht
  have hm' : Float32.isFinite meas = true := hm
  have ht'' : Float32.isNaN target = false := Float32.not_isNaN_of_isFinite ht
  have hm'' : Float32.isNaN meas = false := Float32.not_isNaN_of_isFinite hm
  basic_unfold
  rfl

theorem basic_I (p : AC_PID_Basic.Params) (s : AC_PID_Basic.State) (target meas dt : Float32)
    (ln lp : Bool) (ht : target.IsFinite) (hm : meas.IsFinite) (hr : s._reset_filter = false)
    (hdtp : is_positive_float dt = true) (hki : is_zero_AP_Float p._ki = true) :
    (AC_PID_Basic.update_all_float3_bool2 p s target meas dt ln lp).1._integrator = 0.0 := by
  have ht' : Float32.isFinite target = true := ht
  have hm' : Float32.isFinite meas = true := hm
  have ht'' : Float32.isNaN target = false := Float32.not_isNaN_of_isFinite ht
  have hm'' : Float32.isNaN meas = false := Float32.not_isNaN_of_isFinite hm
  basic_unfold
  rfl

theorem basic_R (p : AC_PID_Basic.Params) (s : AC_PID_Basic.State) (target meas dt : Float32)
    (ln lp : Bool) (ht : target.IsFinite) (hm : meas.IsFinite) (hr : s._reset_filter = false)
    (hdtp : is_positive_float dt = true) (hki : is_zero_AP_Float p._ki = true) :
    (AC_PID_Basic.update_all_float3_bool2 p s target meas dt ln lp).1._reset_filter = false := by
  have ht' : Float32.isFinite target = true := ht
  have hm' : Float32.isFinite meas = true := hm
  have ht'' : Float32.isNaN target = false := Float32.not_isNaN_of_isFinite ht
  have hm'' : Float32.isNaN meas = false := Float32.not_isNaN_of_isFinite hm
  basic_unfold
  rfl

theorem basic_O (p : AC_PID_Basic.Params) (s : AC_PID_Basic.State) (target meas dt : Float32)
    (ln lp : Bool) (ht : target.IsFinite) (hm : meas.IsFinite) (hr : s._reset_filter = false)
    (hdtp : is_positive_float dt = true) (hki : is_zero_AP_Float p._ki = true) :
    let r := AC_PID_Basic.update_all_float3_bool2 p s target meas dt ln lp
    r.2 = r.1._error * p._kp + r.1._integrator + r.1._derivative * p._kd + r.1._target * p._kff := by
  have ht' : Float32.isFinite target = true := ht
  have hm' : Float32.isFinite meas = true := hm
  have ht'' : Float32.isNaN target = false := Float32.not_isNaN_of_isFinite ht
  have hm'' : Float32.isNaN meas = false := Float32.not_isNaN_of_isFinite hm
  basic_unfold
  rfl


/-- `αV = calc_lowpass_alpha_dt(0.0025f, 5)` as a real. -/
def αVr : ℝ := 4886901 / 67108864

/-- The derivative filter step of the PIDs, `d + α ((e⁺ - e)/dt - d)`, stays finite and below
`2³⁰` for `α ∈ [0.07, 1]` and `|e|, |e⁺| ≤ 3 · 2¹⁰`. -/
theorem deriv_step {d e e' α dt : Float32} {αr δα : ℝ} (hd : d.IsFinite) (he : e.IsFinite)
    (he' : e'.IsFinite) (hdt : dt.IsFinite) (hdtv : dt.toReal = dtR) (hα : A32 α αr δα)
    (hα0 : 7 / 100 ≤ αr) (hα1 : αr ≤ 1) (hδ : δα ≤ 1 / 2 ^ 22)
    (hdb : |d.toReal| ≤ 2 ^ 30) (heb : |e.toReal| ≤ 3 * 2 ^ 10) (he'b : |e'.toReal| ≤ 3 * 2 ^ 10) :
    (d + α * ((e' - e) / dt - d)).IsFinite ∧ |(d + α * ((e' - e) / dt - d)).toReal| ≤ 2 ^ 30 := by
  have hη1 := η32_small; have hη0 := η32_pos
  have hu : u32 = 1 / 16777216 := u32_eq
  have hE5 : |e'.toReal - e.toReal| ≤ 6 * 2 ^ 10 := (abs_sub _ _).trans (by linarith)
  have hdE := (A32.of_exact he').sub (A32.of_exact he) (by
    simp only [add_zero]; norm_num [capF]; linarith)
  simp only [add_zero] at hdE
  have hdE' : A32 (e' - e) (e'.toReal - e.toReal) 1 :=
    hdE.mono (by rw [hu]; norm_num at hE5 ⊢; nlinarith)
  have hq := hdE'.div ((A32.of_exact hdt).congr hdtv) (m := 1 / 401) (by norm_num)
    (by rw [dtR]; norm_num) (by
      rw [abs_div, abs_of_pos (by rw [dtR]; norm_num : (0 : ℝ) < dtR), dtR]
      norm_num [capF]; nlinarith)
  have hq' : A32 ((e' - e) / dt) ((e'.toReal - e.toReal) / dtR) (2 ^ 20) :=
    hq.mono (by
      rw [abs_div, abs_of_pos (by rw [dtR]; norm_num : (0 : ℝ) < dtR), dtR, hu]
      norm_num; nlinarith)
  have hqb : |(e'.toReal - e.toReal) / dtR| ≤ 2 ^ 22 := by
    rw [abs_div, abs_of_pos (by rw [dtR]; norm_num : (0 : ℝ) < dtR), dtR, div_le_iff₀ (by norm_num)]
    norm_num at hE5 ⊢; linarith
  have hD' := A32.filt (M := 2 ^ 30) hd hq' hα (by linarith) hα1 (by linarith) (by norm_num)
    (by linarith) hdb (by norm_num)
  refine ⟨hD'.1, ?_⟩
  have h1 := hD'.abs_le
  have h2 : |d.toReal + αr * ((e'.toReal - e.toReal) / dtR - d.toReal)| ≤
      (1 - αr) * 2 ^ 30 + αr * 2 ^ 22 := by
    rw [show d.toReal + αr * ((e'.toReal - e.toReal) / dtR - d.toReal) =
      (1 - αr) * d.toReal + αr * ((e'.toReal - e.toReal) / dtR) by ring]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul, abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 1 - αr),
      abs_of_nonneg (by linarith : (0 : ℝ) ≤ αr)]
    have := mul_le_mul_of_nonneg_left hdb (by linarith : (0 : ℝ) ≤ 1 - αr)
    have := mul_le_mul_of_nonneg_left hqb (by linarith : (0 : ℝ) ≤ αr)
    linarith
  rw [hu] at h1
  have : αr * 2 ^ 20 ≤ 2 ^ 20 := by nlinarith
  have : δα * 2 ^ 30 ≤ 2 ^ 8 := by nlinarith
  have : αr * 2 ^ 30 ≤ 2 ^ 30 := by nlinarith
  nlinarith

/-- **C5 (second half), `AC_PID_Basic::update_all` as `D_update_controller` calls it** (vertical
velocity, `PSC_D_VEL_P 5`, `I = D = FF = 0`, `FLTE = FLTD = 5`): the error filter is the 5 Hz
low-pass step with `αV` and the output is `5 ⟦eV⁺⟧`; the integrator is `0`. -/
theorem vel_pi (hL : LibmSpec) (p : AC_PID_Basic.Params) (s : AC_PID_Basic.State)
    (target meas dt : Float32) (ln lp : Bool) {M : ℝ}
    (hkp : p._kp.IsFinite) (hkpv : p._kp.toReal = 5) (hki : p._ki.IsFinite) (hkiv : p._ki.toReal = 0)
    (hkd : p._kd.IsFinite) (hkdv : p._kd.toReal = 0) (hkff : p._kff.IsFinite)
    (hkffv : p._kff.toReal = 0) (hfE : p._filt_E_hz.IsFinite) (hfEv : p._filt_E_hz.toReal = 5)
    (hfD : p._filt_D_hz.IsFinite) (hfDv : p._filt_D_hz.toReal = 5)
    (hdt : dt.IsFinite) (hdtv : dt.toReal = dtR) (hr : s._reset_filter = false)
    (hE : s._error.IsFinite) (hD : s._derivative.IsFinite) (ht : target.IsFinite)
    (hm : meas.IsFinite) (hM1 : 1 ≤ M) (hM : M ≤ 2 ^ 10) (htM : |target.toReal| ≤ M)
    (hmM : |meas.toReal| ≤ M) (hEM : |s._error.toReal| ≤ 2 * M) (hDM : |s._derivative.toReal| ≤ 2 ^ 30) :
    let r := AC_PID_Basic.update_all_float3_bool2 p s target meas dt ln lp
    A32 r.1._error (s._error.toReal + αVr * ((target.toReal - meas.toReal) - s._error.toReal))
      (40 * u32 * M + 4 * η32) ∧
    A32 r.2 (5 * r.1._error.toReal) (16 * u32 * M + η32) ∧
    r.1._reset_filter = false ∧ r.1._derivative.IsFinite ∧ |r.1._derivative.toReal| ≤ 2 ^ 30 ∧
    |r.1._error.toReal| ≤ 3 * M ∧ r.1._integrator = 0.0 := by
  intro r
  have hη1 := η32_small; have hη0 := η32_pos
  have hu : u32 = 1 / 16777216 := u32_eq
  have hdtp : is_positive_float dt = true := by rw [isPos_iff hdt, hdtv, dtR]; norm_num
  have hkiz : is_zero_AP_Float p._ki = true := by
    show is_zero_float p._ki = true
    rw [isZero_iff hki, hkiv]; norm_num
  have eT := basic_T p s target meas dt ln lp ht hm hr hdtp hkiz
  have eE := basic_E p s target meas dt ln lp ht hm hr hdtp hkiz
  have eD := basic_D p s target meas dt ln lp ht hm hr hdtp hkiz
  have eI := basic_I p s target meas dt ln lp ht hm hr hdtp hkiz
  have eR := basic_R p s target meas dt ln lp ht hm hr hdtp hkiz
  have eO := basic_O p s target meas dt ln lp ht hm hr hdtp hkiz
  have aE : A32 (AC_PID_Basic.get_filt_E_alpha p dt) αVr (1 / 2 ^ 22) := alpha5 hL hdt hdtv hfE hfEv
  have aD : A32 (AC_PID_Basic.get_filt_D_alpha p dt) αVr (1 / 2 ^ 22) := alpha5 hL hdt hdtv hfD hfDv
  -- the error filter
  have hx := (A32.of_exact ht).sub (A32.of_exact hm) (by
    simp only [add_zero]; have := abs_sub target.toReal meas.toReal; norm_num [capF]; nlinarith)
  simp only [add_zero, zero_add] at hx
  have hx' : A32 (target - meas) (target.toReal - meas.toReal) (2 * u32 * M + η32) :=
    hx.mono (by have := abs_sub target.toReal meas.toReal; rw [hu]; nlinarith)
  have hE' : A32 r.1._error (s._error.toReal + αVr * ((target.toReal - meas.toReal) - s._error.toReal))
      (40 * u32 * M + 4 * η32) := by
    rw [eE]
    have := A32.filt (M := 2 * M) hE hx' aE (by rw [αVr]; norm_num) (by rw [αVr]; norm_num)
      (by norm_num) (by rw [hu]; nlinarith) ((abs_sub _ _).trans (by linarith)) hEM (by linarith)
    refine this.mono ?_
    rw [hu, αVr]; nlinarith
  have hE'b : |r.1._error.toReal| ≤ 3 * M := by
    have h1 := hE'.abs_le
    have h2 : |s._error.toReal + αVr * ((target.toReal - meas.toReal) - s._error.toReal)| ≤ 2 * M := by
      rw [show s._error.toReal + αVr * ((target.toReal - meas.toReal) - s._error.toReal) =
        (1 - αVr) * s._error.toReal + αVr * (target.toReal - meas.toReal) by ring]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_of_nonneg (by rw [αVr]; norm_num : (0 : ℝ) ≤ 1 - αVr),
        abs_of_nonneg (by rw [αVr]; norm_num : (0 : ℝ) ≤ αVr)]
      have := abs_sub target.toReal meas.toReal
      have := mul_le_mul_of_nonneg_left hEM (by rw [αVr]; norm_num : (0 : ℝ) ≤ 1 - αVr)
      have := mul_le_mul_of_nonneg_left (show |target.toReal - meas.toReal| ≤ 2 * M by linarith)
        (by rw [αVr]; norm_num : (0 : ℝ) ≤ αVr)
      linarith
    rw [hu] at h1; nlinarith
  -- the derivative filter
  obtain ⟨hD'f, hD'b⟩ := deriv_step hD hE hE'.1 hdt hdtv aD (by rw [αVr]; norm_num)
    (by rw [αVr]; norm_num) le_rfl hDM (by linarith) (by linarith)
  rw [← eD] at hD'f hD'b
  -- the output
  have hP := (A32.of_exact hE'.1).mul ((A32.of_exact hkp).congr hkpv) (by
    simp only [mul_zero, zero_mul, add_zero, abs_zero]; rw [abs_mul]; norm_num [capF]; nlinarith)
  simp only [mul_zero, zero_mul, add_zero, abs_zero, zero_add] at hP
  have hI0 : r.1._integrator.IsFinite ∧ r.1._integrator.toReal = 0 := by
    rw [eI]; exact ⟨Float32.isFinite_lit_zero, Float32.toReal_lit_zero⟩
  obtain ⟨s1f, s1v⟩ := f32_add_zero hP.1 hI0.1 hI0.2
  obtain ⟨q1f, q1v⟩ := f32_mul_zero hD'f hkd hkdv
  obtain ⟨s2f, s2v⟩ := f32_add_zero s1f q1f q1v
  have hTf : r.1._target.IsFinite := by rw [eT]; exact ht
  obtain ⟨q2f, q2v⟩ := f32_mul_zero hTf hkff hkffv
  obtain ⟨s3f, s3v⟩ := f32_add_zero s2f q2f q2v
  refine ⟨hE', ⟨eO ▸ s3f, ?_⟩, eR, hD'f, hD'b, hE'b, eI⟩
  rw [eO, s3v, s2v, s1v, mul_comm (5 : ℝ)]
  refine hP.2.trans ?_
  rw [abs_mul, show |(5 : ℝ)| = 5 by norm_num, hu]
  nlinarith [abs_nonneg r.1._error.toReal]


theorem f32_div_exact {a b c : Float32} (ha : a.IsFinite) (hb : b.IsFinite) (hc : c.IsFinite)
    (hb0 : b.toReal ≠ 0) (h : a.toReal / b.toReal = c.toReal) :
    (a / b).IsFinite ∧ (a / b).toReal = c.toReal := by
  have hm : |a.toReal / b.toReal| ≤ maxFinite32 := h ▸ Float32.abs_toReal_le_maxFinite c
  obtain ⟨hf, -⟩ := Float32.div_err_all ha hb hb0 hm
  have := Float32.div_bracket ha hb hb0 hm hc
  exact ⟨hf, le_antisymm (this.2 h.le) (this.1 h.ge)⟩

theorem f64_add_exact {a b c : Float} (ha : a.IsFinite) (hb : b.IsFinite) (hc : c.IsFinite)
    (h : a.toReal + b.toReal = c.toReal) : (a + b).IsFinite ∧ (a + b).toReal = c.toReal := by
  have hm : |a.toReal + b.toReal| ≤ maxFinite := by
    rw [h]; exact Float.abs_toReal_le_maxFinite c
  obtain ⟨hf, -⟩ := Float.add_err_all ha hb hm
  have := Float.add_bracket ha hb hm hc
  exact ⟨hf, le_antisymm (this.2 h.le) (this.1 h.ge)⟩

/-- `sqrt_controller(error, p = 1, D1, dt = 0)` in its linear zone `|error| < D1` is `error`. -/
theorem sqrt_lin (hL : LibmSpec) {err kp D1 : Float32} (he : err.IsFinite) (hkp : kp.IsFinite)
    (hkpv : kp.toReal = 1) (hD : D1.IsFinite) (hD0 : 2 ^ (-23 : ℤ) ≤ D1.toReal)
    (hlin : |err.toReal| < D1.toReal) :
    (sqrt_controller_float4 err kp D1 (Float.toFloat32 (0.0 : Float))).IsFinite ∧
      (sqrt_controller_float4 err kp D1 (Float.toFloat32 (0.0 : Float))).toReal = err.toReal := by
  have hn : is_negative_float D1 = false := isNeg_false hL hD (by
    have : (0 : ℝ) < 2 ^ (-23 : ℤ) := by positivity
    linarith)
  have hz : is_zero_float D1 = false := by
    rw [Bool.eq_false_iff, ne_eq, isZero_iff hD, abs_of_pos (lt_of_lt_of_le (by positivity) hD0)]
    exact not_lt.2 hD0
  have hzp : is_zero_float kp = false := by
    rw [Bool.eq_false_iff, ne_eq, isZero_iff hkp, hkpv]; norm_num
  obtain ⟨z0f, z0v⟩ := f32_ofF64_zero hL
  have hpz : is_positive_float (Float.toFloat32 (0.0 : Float)) = false := by
    rw [Bool.eq_false_iff, ne_eq, isPos_iff z0f, z0v]; norm_num
  obtain ⟨sqf, sqv⟩ := f32_mul_one hkp hkp hkpv
  rw [hkpv] at sqv
  obtain ⟨ldf, ldv⟩ := f32_div_exact hD sqf hD (by rw [sqv]; norm_num) (by rw [sqv, div_one])
  have hgt : ¬ (err > D1 / sq_float kp) := by
    show ¬ (D1 / (kp * kp) < err)
    rw [Float32.lt_iff_toReal_lt ldf he, ldv, not_lt]
    exact (le_abs_self _).trans hlin.le
  have hlt : ¬ (err < -(D1 / sq_float kp)) := by
    show ¬ (err < -(D1 / (kp * kp)))
    rw [Float32.lt_iff_toReal_lt he ((Float32.isFinite_neg _).2 ldf), Float32.toReal_neg, ldv, not_lt]
    have := neg_abs_le err.toReal
    linarith
  simp only [sqrt_controller_float4, Id.run, hn, hz, hzp, hpz, hgt, hlt, Bool.or_self,
    Bool.false_eq_true, ite_false, id_pure_eq]
  exact f32_mul_one he hkp hkpv

/-- **C5 (first half), `AC_P_1D::update_all`** (vertical position, `PSC_D_POS_P 1`) inside the
linear zone of the sqrt controller and the error limits (`|target - pos| ≤ E` with
`2E ≤ min(D1_max, -error_min, error_max)`): the target is unchanged, and the velocity output and
the stored error are `(float)(target - pos)`, within `2u E + 2η` of `target - pos`. -/
theorem pos_p (hL : LibmSpec) (p : AC_P_1D.Params) (s : AC_P_1D.State) (target meas : Float) {E : ℝ}
    (hkp : p._kp.IsFinite) (hkpv : p._kp.toReal = 1) (ht : target.IsFinite) (hm : meas.IsFinite)
    (hE0 : 1 / 2 ^ 20 ≤ E)
    (hE1 : E ≤ 2 ^ 10) (hE : |target.toReal - meas.toReal| ≤ E)
    (hmin : s._error_min.IsFinite) (hminv : s._error_min.toReal ≤ -(2 * E))
    (hmax : s._error_max.IsFinite) (hmaxv : 2 * E ≤ s._error_max.toReal)
    (hD1 : s._D1_max.IsFinite) (hD1v : 2 * E ≤ s._D1_max.toReal) :
    let r := AC_P_1D.update_all p s target meas
    r.2.1 = target ∧ A32 r.2.2 (target.toReal - meas.toReal) (2 * u32 * E + 2 * η32) ∧
      A32 r.1._error (target.toReal - meas.toReal) (2 * u32 * E + 2 * η32) := by
  intro r
  have hη1 := η32_small; have hη0 := η32_pos
  have hη64 := η64_small; have hη64' := η64_pos
  have hu : u32 = 1 / 16777216 := u32_eq
  have hu64 : u64 = 1 / 9007199254740992 := by norm_num [u64]
  -- the error, `(float)(target - measurement)`
  have d1 := (A64.of_exact ht).sub (A64.of_exact hm) (by
    simp only [add_zero]; have := abs_sub target.toReal meas.toReal; norm_num [capF]; linarith)
  simp only [add_zero, zero_add] at d1
  have d2 := d1.toFloat32 hL (by
    rw [hu64]; norm_num [capF]; nlinarith)
  have d3 : A32 (Float.toFloat32 (target - meas)) (target.toReal - meas.toReal)
      (2 * u32 * E + 2 * η32) := d2.mono (by
    have h64 : η64 ≤ η32 := by rw [η64_eq, η32_eq]; exact zpow_le_zpow_right₀ one_le_two (by norm_num)
    rw [hu, hu64]; nlinarith)
  have hEb : |(Float.toFloat32 (target - meas)).toReal| < 2 * E := by
    have := d3.abs_le; rw [hu] at this; nlinarith
  have hc1 : decide (Float.toFloat32 (target - meas) < s._error_min) = false := by
    rw [decide_eq_false_iff_not, Float32.lt_iff_toReal_lt d3.1 hmin, not_lt]
    have := neg_abs_le (Float.toFloat32 (target - meas)).toReal
    linarith
  have hc2 : decide (Float.toFloat32 (target - meas) > s._error_max) = false := by
    rw [decide_eq_false_iff_not, gt_iff_lt, Float32.lt_iff_toReal_lt hmax d3.1, not_lt]
    exact (le_abs_self _).trans (by linarith)
  have hsq := sqrt_lin hL d3.1 hkp hkpv hD1 (by
    rw [show (2 : ℝ) ^ (-23 : ℤ) = 1 / 8388608 by norm_num]; norm_num at hE0; linarith) (by linarith)
  have e1 : r = ({ s with _error := Float.toFloat32 (target - meas) }, target,
      sqrt_controller_float4 (Float.toFloat32 (target - meas)) p._kp s._D1_max
        (Float.toFloat32 (0.0 : Float))) := by
    simp only [r, AC_P_1D.update_all, Id.run, hc1, hc2, Bool.and_false, Bool.false_eq_true,
      ite_false, id_pure_eq]
  rw [e1]
  exact ⟨rfl, ⟨hsq.1, by rw [hsq.2]; exact d3.2⟩, d3⟩
end Basic

/-! ## Sharp forms: exact coefficients (`PiF32`), error-scale magnitudes -/

section PID2
open AC_PosControl_lib

theorem integ_step2 {I e ki dt k : Float32} {M : ℝ} (hI : I.IsFinite) (he : e.IsFinite)
    (hki : ki.IsFinite) (hkiv : ki.toReal = kiA) (hdt : dt.IsFinite) (hdtv : dt.toReal = dtR)
    (hk : k.IsFinite) (hk' : k.toReal ≤ 2) (hM1 : 1 / 8 ≤ M) (hM : M ≤ 2 ^ 10)
    (heM : |e.toReal| ≤ 3 * M) (himax : |I.toReal| + M / 2 ^ 10 ≤ k.toReal) (l : UInt32) :
    A32 (constrain_value_line_float (I + e * ki * 1.0 * dt) (-k) k l)
      (I.toReal + kiA * dtR * e.toReal) (u32 * |I.toReal| + u32 * M / 2 ^ 7 + 4 * η32) ∧
    |(constrain_value_line_float (I + e * ki * 1.0 * dt) (-k) k l).toReal| ≤ k.toReal := by
  have hη1 := η32_small; have hη0 := η32_pos
  have hu : u32 = 1 / 16777216 := u32_eq
  have hki' : A32 ki kiA 0 := (A32.of_exact hki).congr hkiv
  have hdt' : A32 dt dtR 0 := (A32.of_exact hdt).congr hdtv
  have hea := abs_nonneg e.toReal
  have hEk : |e.toReal * kiA| ≤ 3 * M / 2 ^ 3 := by
    rw [abs_mul, kiA]; norm_num; nlinarith
  have i1 := (A32.of_exact he).mul hki' (by
    simp only [mul_zero, zero_mul, add_zero, abs_zero]; have := hEk; norm_num [capF] at this ⊢; linarith)
  obtain ⟨i2f, i2v⟩ := f32_mul_one i1.1 Float32.isFinite_lit_one Float32.toReal_lit_one
  have i2 : A32 (e * ki * 1.0) (e.toReal * kiA) (u32 * (3 * M / 2 ^ 3) + η32) := ⟨i2f, by
    rw [i2v]; have := i1.2; simp only [mul_zero, zero_mul, add_zero, abs_zero, zero_add] at this
    have h2 : u32 * |e.toReal * kiA| ≤ u32 * (3 * M / 2 ^ 3) := mul_le_mul_of_nonneg_left hEk u32_pos.le
    exact this.trans (by linarith)⟩
  have hEkd : |e.toReal * kiA * dtR| ≤ M / 1300 := by
    rw [abs_mul, abs_mul, kiA, dtR]; norm_num; nlinarith
  have i3 := i2.mul hdt' (by
    simp only [mul_zero, zero_mul, add_zero, abs_zero]
    rw [abs_of_pos (by rw [dtR]; norm_num : (0 : ℝ) < dtR)]
    have := hEk; rw [hu, dtR]; norm_num [capF] at this ⊢; nlinarith)
  have i3' : A32 (e * ki * 1.0 * dt) (e.toReal * kiA * dtR) (u32 * M / 2 ^ 8 + 2 * η32) := by
    refine i3.mono ?_
    simp only [mul_zero, zero_mul, add_zero, abs_zero, zero_add]
    rw [abs_of_pos (by rw [dtR]; norm_num : (0 : ℝ) < dtR)]
    have := hEk; rw [hu, dtR]; norm_num at this ⊢; nlinarith
  have hIa := abs_nonneg I.toReal
  have hadd := abs_add_le I.toReal (e.toReal * kiA * dtR)
  have i4 := (A32.of_exact hI).add i3' (by
    simp only [add_zero, zero_add]; rw [hu] at *; norm_num [capF]; nlinarith)
  have i4' : A32 (I + e * ki * 1.0 * dt) (I.toReal + kiA * dtR * e.toReal)
      (u32 * |I.toReal| + u32 * M / 2 ^ 7 + 4 * η32) := by
    refine (i4.mono ?_).congr (by ring)
    simp only [zero_add]
    rw [hu] at *; nlinarith
  have hcl : |(I + e * ki * 1.0 * dt).toReal| ≤ k.toReal := by
    have h1 := i4'.abs_le
    have h2 : |I.toReal + kiA * dtR * e.toReal| ≤ |I.toReal| + M / 1300 := by
      rw [show kiA * dtR * e.toReal = e.toReal * kiA * dtR by ring]; linarith
    have hI10 : |I.toReal| ≤ 2 := by linarith
    rw [hu] at h1; norm_num at h1 h2 himax hI10 ⊢; linarith
  obtain ⟨fc, ec⟩ := constrain_spec l i4'.1 ((Float32.isFinite_neg _).2 hk) hk
    (by rw [Float32.toReal_neg]; linarith)
  rw [Float32.toReal_neg] at ec
  have hcl' := abs_le.1 hcl
  rw [min_eq_right hcl'.2, max_eq_right hcl'.1] at ec
  exact ⟨⟨fc, by rw [ec]; exact i4'.2⟩, by rw [ec]; exact hcl⟩


theorem pd_out2 {e kp Dm D kd I : Float32} {M K : ℝ} (he : e.IsFinite) (hkp : kp.IsFinite)
    (hkpv : kp.toReal = kpA) (hDm : Dm.IsFinite) (hDmv : Dm.toReal = 1) (hD : D.IsFinite)
    (hkd : kd.IsFinite) (hkdv : kd.toReal = 0) (hI : I.IsFinite) (hM1 : 1 / 8 ≤ M) (hM : M ≤ 2 ^ 10)
    (heM : |e.toReal| ≤ 3 * M) (hIK : |I.toReal| ≤ K) (hK : K ≤ 2 ^ 10) :
    A32 (e * kp * Dm * 1.0 + D * kd * Dm * 1.0 + I) (kpA * e.toReal + I.toReal)
      (u32 * (M / 2 + K) + 4 * η32) := by
  have hη1 := η32_small; have hη0 := η32_pos
  have hu : u32 = 1 / 16777216 := u32_eq
  have hek : |e.toReal * kpA| ≤ 3 * M / 2 ^ 4 := by
    rw [abs_mul, kpA]; norm_num; nlinarith [abs_nonneg e.toReal]
  have p1 := (A32.of_exact he).mul ((A32.of_exact hkp).congr hkpv) (by
    simp only [mul_zero, zero_mul, add_zero, abs_zero]; have := hek; norm_num [capF] at this ⊢; linarith)
  simp only [mul_zero, zero_mul, add_zero, abs_zero, zero_add] at p1
  obtain ⟨p2f, p2v⟩ := f32_mul_one p1.1 hDm hDmv
  obtain ⟨p3f, p3v⟩ := f32_mul_one p2f Float32.isFinite_lit_one Float32.toReal_lit_one
  obtain ⟨q1f, q1v⟩ := f32_mul_zero hD hkd hkdv
  obtain ⟨q2f, q2v⟩ := f32_mul_exact q1f hDm Float32.isFinite_lit_zero (by
    rw [q1v, zero_mul, Float32.toReal_lit_zero])
  rw [Float32.toReal_lit_zero] at q2v
  obtain ⟨q3f, q3v⟩ := f32_mul_exact q2f Float32.isFinite_lit_one Float32.isFinite_lit_zero (by
      rw [q2v, zero_mul, Float32.toReal_lit_zero])
  rw [Float32.toReal_lit_zero] at q3v
  obtain ⟨s1f, s1v⟩ := f32_add_zero p3f q3f q3v
  have s1 : A32 (e * kp * Dm * 1.0 + D * kd * Dm * 1.0) (e.toReal * kpA)
      (u32 * |e.toReal * kpA| + η32) := ⟨s1f, by rw [s1v, p3v, p2v]; exact p1.2⟩
  have hadd := abs_add_le (e.toReal * kpA) I.toReal
  have s2 := s1.add (A32.of_exact hI) (by
    simp only [add_zero]; have := hek; rw [hu]; norm_num [capF] at this ⊢; nlinarith)
  refine (s2.mono ?_).congr (by ring)
  simp only [add_zero]
  rw [hu] at *; nlinarith [abs_nonneg (e.toReal * kpA)]


/-- `αA` as a real. -/
def αAr : ℝ := 16042859 / 67108864

set_option maxHeartbeats 4000000 in
/-- **C6, sharp form.** `accel_pid` with the coefficients exact (`PiF32`), the period `0.0025f`,
signal magnitudes `≤ Ma` (target filter, target) and error magnitudes `≤ Me`
(`|target - meas|`, the error filter): the `β`s scale with `Me` except the target filter's
`5.13 u Ma`. -/
theorem accel_pid2 (hL : LibmSpec) (hpi : PiF32) (p : AC_PID.Params) (s : AC_PID.State)
    (inp : AC_PID.Inputs) (target meas dt : Float32) {Ma Me : ℝ}
    (hkp : p._kp.IsFinite) (hkpv : p._kp.toReal = kpA)
    (hki : p._ki.IsFinite) (hkiv : p._ki.toReal = kiA)
    (hkd : p._kd.IsFinite) (hkdv : p._kd.toReal = 0)
    (hkff : p._kff.IsFinite) (hkffv : p._kff.toReal = 0)
    (hkdff : p._kdff.IsFinite) (hkdffv : p._kdff.toReal = 0)
    (hpd : p._kpdmax.IsFinite) (hpdv : p._kpdmax.toReal = 0)
    (hsr : p._slew_rate_max.IsFinite) (hsrv : p._slew_rate_max.toReal = 0)
    (hfT : p._filt_T_hz.IsFinite) (hfTv : p._filt_T_hz.toReal = 0)
    (hfE : p._filt_E_hz = 20.0)
    (hfD : p._filt_D_hz.IsFinite) (hfDv : p._filt_D_hz.toReal = 0)
    (himx : p._kimax.IsFinite) (himx' : p._kimax.toReal ≤ 2)
    (hdt : dt = d0) (hr : s._flags._reset_filter = false)
    (hT : s._target.IsFinite) (hE : s._error.IsFinite) (hI : s._integrator.IsFinite)
    (hD : s._derivative.IsFinite) (ht : target.IsFinite) (hm : meas.IsFinite)
    (hMa1 : 1 ≤ Ma) (hMa : Ma ≤ 2 ^ 10) (hMe1 : 1 / 8 ≤ Me) (hMe : Me ≤ 2 ^ 10)
    (hMaMe : Ma ≤ 2 ^ 10 * Me)
    (hTM : |s._target.toReal| ≤ Ma) (htM : |target.toReal| ≤ Ma)
    (hdM : |target.toReal - meas.toReal| ≤ Me) (hEM : |s._error.toReal| ≤ Me)
    (hDM : |s._derivative.toReal| ≤ 2 ^ 30)
    (himax : |s._integrator.toReal| + Me / 2 ^ 10 ≤ p._kimax.toReal) :
    let r := AC_PID.update_all p s inp target meas dt false 1.0 1.0
    A32 r.1._target target.toReal (513 / 100 * u32 * Ma + 2 * η32) ∧
    A32 r.1._error (s._error.toReal + αAr * ((target.toReal - meas.toReal) - s._error.toReal))
      (αAr * (514 / 100 * u32 * Ma + u32 * Me + 4 * η32) + (102 / 100 + 411 / 100 * αAr) * u32 * Me +
        2 * η32) ∧
    A32 r.1._integrator (s._integrator.toReal + kiA * dtR * r.1._error.toReal)
        (u32 * |s._integrator.toReal| + u32 * Me / 2 ^ 7 + 4 * η32) ∧
    A32 r.2 (kpA * r.1._error.toReal + r.1._integrator.toReal)
        (u32 * (Me / 2 + p._kimax.toReal) + 4 * η32) ∧
    (AC_PID.get_ff r.1).IsFinite ∧ (AC_PID.get_ff r.1).toReal = 0 ∧
    r.1._flags._reset_filter = false ∧ r.1._derivative.IsFinite ∧
    |r.1._derivative.toReal| ≤ 2 ^ 30 ∧ |r.1._error.toReal| ≤ 2 * Me := by
  intro r
  subst hdt
  have hη1 := η32_small; have hη0 := η32_pos
  have hu : u32 = 1 / 16777216 := u32_eq
  have hdtf := d0_fin; have hdtv := d0_val
  -- the branch conditions
  have hdtp : is_positive_float d0 = true := by rw [isPos_iff hdtf, hdtv, dtR]; norm_num
  have hkiz : is_zero_AP_Float p._ki = false := by
    show is_zero_float p._ki = false
    rw [Bool.eq_false_iff, ne_eq, isZero_iff hki, hkiv, kiA]; norm_num
  have hsr' : p._slew_rate_max ≤ Int32.toFloat32 (0 : Int32) := by
    rw [Float32.le_iff_toReal_le hsr Float32.isFinite_int32_zero, hsrv, Float32.toReal_int32_zero]
  have hpd' : is_positive_AP_Float p._kpdmax = false := by
    rw [Bool.eq_false_iff, ne_eq, isPosAP_iff hpd, hpdv]; norm_num
  have eT := pid_T p s inp target meas d0 ht hm hr hdtp hkiz hpd'
  have eE := pid_E p s inp target meas d0 ht hm hr hdtp hkiz hpd'
  have eI := pid_I p s inp target meas d0 ht hm hr hdtp hkiz hpd'
  have eD := pid_D p s inp target meas d0 ht hm hr hdtp hkiz hpd'
  have eTd := pid_Td p s inp target meas d0 ht hm hr hdtp hkiz hpd'
  have eR := pid_R p s inp target meas d0 ht hm hr hdtp hkiz hpd'
  have eFF := pid_FF p s inp target meas d0 ht hm hr hdtp hkiz hpd'
  have eDFF := pid_DFF p s inp target meas d0 ht hm hr hdtp hkiz hpd'
  have eO := pid_O p s inp target meas d0 ht hm hr hdtp hkiz hpd'
  obtain ⟨X, Y, eDm⟩ := pid_X p s inp target meas d0 ht hm hr hdtp hkiz hpd'
  have hDm : r.1._pid_info.Dmod.IsFinite ∧ r.1._pid_info.Dmod.toReal = 1 := by
    rw [eDm, modifier_snd _ _ _ _ _ _ hsr']; exact f32_ofF64_one hL
  -- the coefficients
  have aT : A32 (AC_PID.get_filt_T_alpha p d0) 1 0 :=
    alpha0 hL hdtf (by rw [hdtv, dtR]; norm_num) hfT hfTv
  have aE : A32 (AC_PID.get_filt_E_alpha p d0) αAr 0 := by
    show A32 (calc_lowpass_alpha_dt d0 p._filt_E_hz) αAr 0
    rw [hfE]; exact alphaA hL hpi
  have aD : A32 (AC_PID.get_filt_D_alpha p d0) 1 0 :=
    alpha0 hL hdtf (by rw [hdtv, dtR]; norm_num) hfD hfDv
  -- the target filter
  have hT' : A32 r.1._target target.toReal (513 / 100 * u32 * Ma + 2 * η32) := by
    rw [eT]
    have := A32.filt2 hT (A32.of_exact ht) aT (by norm_num) le_rfl (by norm_num) (by positivity)
      htM hTM (by linarith)
    simp only [mul_zero, zero_add, one_mul, add_sub_cancel] at this
    refine this.mono (le_of_eq ?_); ring
  -- the error
  have herr := hT'.sub (A32.of_exact hm) (by
    rw [hu]; norm_num [capF]; nlinarith)
  have herr' : A32 (r.1._target - meas) (target.toReal - meas.toReal)
      (514 / 100 * u32 * Ma + u32 * Me + 4 * η32) := by
    refine herr.mono ?_
    rw [hu] at *; nlinarith
  have hE' : A32 r.1._error (s._error.toReal + αAr * ((target.toReal - meas.toReal) - s._error.toReal))
      (αAr * (514 / 100 * u32 * Ma + u32 * Me + 4 * η32) + (102 / 100 + 411 / 100 * αAr) * u32 * Me +
        2 * η32) := by
    rw [eE]
    have := A32.filt2 (M := Me) hE herr' aE (by rw [αAr]; norm_num) (by rw [αAr]; norm_num)
      (by norm_num) (by rw [hu]; nlinarith) hdM hEM (by linarith)
    refine this.mono (le_of_eq ?_); ring
  have hE'b : |r.1._error.toReal| ≤ 2 * Me := by
    have h1 := hE'.abs_le
    have h2 : |s._error.toReal + αAr * ((target.toReal - meas.toReal) - s._error.toReal)| ≤ Me := by
      rw [show s._error.toReal + αAr * ((target.toReal - meas.toReal) - s._error.toReal) =
        (1 - αAr) * s._error.toReal + αAr * (target.toReal - meas.toReal) by ring]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_of_nonneg (by rw [αAr]; norm_num : (0 : ℝ) ≤ 1 - αAr),
        abs_of_nonneg (by rw [αAr]; norm_num : (0 : ℝ) ≤ αAr)]
      have := mul_le_mul_of_nonneg_left hEM (by rw [αAr]; norm_num : (0 : ℝ) ≤ 1 - αAr)
      have := mul_le_mul_of_nonneg_left hdM (by rw [αAr]; norm_num : (0 : ℝ) ≤ αAr)
      linarith
    rw [hu] at h1
    have h3 : αAr * (514 / 100 * (1 / 16777216) * Ma + 1 / 16777216 * Me + 4 * η32) +
        (102 / 100 + 411 / 100 * αAr) * (1 / 16777216) * Me + 2 * η32 ≤ Me := by
      rw [αAr]; nlinarith
    linarith
  have hE'3 : |r.1._error.toReal| ≤ 3 * Me := by linarith
  -- the integrator
  obtain ⟨hI', hIk⟩ := integ_step2 (l := Int32.toUInt32 346) hI hE'.1 hki hkiv hdtf hdtv himx himx'
    hMe1 hMe hE'3 himax
  rw [← eI] at hI' hIk
  -- the derivative filter
  obtain ⟨hD'f, hD'b⟩ := deriv_step hD hE hE'.1 hdtf hdtv aD (by norm_num) le_rfl (by norm_num) hDM
    (by linarith) (by linarith)
  rw [← eD] at hD'f hD'b
  -- the output
  have hO := pd_out2 hE'.1 hkp hkpv hDm.1 hDm.2 hD'f hkd hkdv hI'.1 hMe1 hMe hE'3 hIk
    (by linarith)
  rw [← eO] at hO
  -- the feedforward
  have hTd : r.1._target_derivative.IsFinite := by
    rw [eTd]
    have h1 := hT'.sub (A32.of_exact hT) (by
      simp only [add_zero]; rw [hu]; norm_num [capF]; have := abs_sub target.toReal s._target.toReal; nlinarith)
    have h2 := h1.div ((A32.of_exact hdtf).congr hdtv) (m := 1 / 401) (by norm_num)
      (by rw [dtR]; norm_num) (by
        rw [abs_div, abs_of_pos (by rw [dtR]; norm_num : (0 : ℝ) < dtR), dtR]
        have := abs_sub target.toReal s._target.toReal
        rw [hu]; norm_num [capF]; nlinarith)
    exact h2.1
  obtain ⟨fF, vF⟩ := f32_mul_zero hT'.1 hkff hkffv
  obtain ⟨fDF, vDF⟩ := f32_mul_zero hTd hkdff hkdffv
  rw [← eFF] at fF vF
  rw [← eDFF] at fDF vDF
  obtain ⟨fff, vff⟩ := f32_add_exact fF fDF Float32.isFinite_lit_zero (by
    rw [vF, vDF, Float32.toReal_lit_zero, add_zero])
  rw [Float32.toReal_lit_zero] at vff
  exact ⟨hT', hE', hI', hO, fff, vff, eR, hD'f, hD'b, hE'b⟩

/-- **C5 (velocity PI), sharp form**: `vel_pi` with the coefficients exact (`PiF32`), the period
`0.0025f`, and the error magnitudes `|target - meas|, |eV| ≤ Me`. -/
theorem vel_pi2 (hL : LibmSpec) (hpi : PiF32) (p : AC_PID_Basic.Params) (s : AC_PID_Basic.State)
    (target meas dt : Float32) (ln lp : Bool) {Me : ℝ}
    (hkp : p._kp.IsFinite) (hkpv : p._kp.toReal = 5) (hki : p._ki.IsFinite) (hkiv : p._ki.toReal = 0)
    (hkd : p._kd.IsFinite) (hkdv : p._kd.toReal = 0) (hkff : p._kff.IsFinite)
    (hkffv : p._kff.toReal = 0) (hfE : p._filt_E_hz = 5.0) (hfD : p._filt_D_hz = 5.0)
    (hdt : dt = d0) (hr : s._reset_filter = false)
    (hE : s._error.IsFinite) (hD : s._derivative.IsFinite) (ht : target.IsFinite)
    (hm : meas.IsFinite) (hMe1 : 1 / 8 ≤ Me) (hMe : Me ≤ 2 ^ 10)
    (hdM : |target.toReal - meas.toReal| ≤ Me) (hEM : |s._error.toReal| ≤ Me)
    (hDM : |s._derivative.toReal| ≤ 2 ^ 30) :
    let r := AC_PID_Basic.update_all_float3_bool2 p s target meas dt ln lp
    A32 r.1._error (s._error.toReal + αVr * ((target.toReal - meas.toReal) - s._error.toReal))
      (αVr * (u32 * Me + η32) + (102 / 100 + 411 / 100 * αVr) * u32 * Me + 2 * η32) ∧
    A32 r.2 (5 * r.1._error.toReal) (10 * u32 * Me + η32) ∧
    r.1._reset_filter = false ∧ r.1._derivative.IsFinite ∧ |r.1._derivative.toReal| ≤ 2 ^ 30 ∧
    |r.1._error.toReal| ≤ 2 * Me ∧ r.1._integrator = 0.0 := by
  intro r
  subst hdt
  have hη1 := η32_small; have hη0 := η32_pos
  have hu : u32 = 1 / 16777216 := u32_eq
  have hdtf := d0_fin; have hdtv := d0_val
  have hdtp : is_positive_float d0 = true := by rw [isPos_iff hdtf, hdtv, dtR]; norm_num
  have hkiz : is_zero_AP_Float p._ki = true := by
    show is_zero_float p._ki = true
    rw [isZero_iff hki, hkiv]; norm_num
  have eE := basic_E p s target meas d0 ln lp ht hm hr hdtp hkiz
  have eD := basic_D p s target meas d0 ln lp ht hm hr hdtp hkiz
  have eI := basic_I p s target meas d0 ln lp ht hm hr hdtp hkiz
  have eR := basic_R p s target meas d0 ln lp ht hm hr hdtp hkiz
  have eO := basic_O p s target meas d0 ln lp ht hm hr hdtp hkiz
  have eT := basic_T p s target meas d0 ln lp ht hm hr hdtp hkiz
  have aE : A32 (AC_PID_Basic.get_filt_E_alpha p d0) αVr 0 := by
    show A32 (calc_lowpass_alpha_dt d0 p._filt_E_hz) αVr 0
    rw [hfE]; exact alphaV hL hpi
  have aD : A32 (AC_PID_Basic.get_filt_D_alpha p d0) αVr 0 := by
    show A32 (calc_lowpass_alpha_dt d0 p._filt_D_hz) αVr 0
    rw [hfD]; exact alphaV hL hpi
  -- the error filter
  have hx := (A32.of_exact ht).sub (A32.of_exact hm) (by
    simp only [add_zero]; norm_num [capF]; linarith)
  simp only [add_zero, zero_add] at hx
  have hx' : A32 (target - meas) (target.toReal - meas.toReal) (u32 * Me + η32) :=
    hx.mono (by have := mul_le_mul_of_nonneg_left hdM u32_pos.le; linarith)
  have hE' : A32 r.1._error (s._error.toReal + αVr * ((target.toReal - meas.toReal) - s._error.toReal))
      (αVr * (u32 * Me + η32) + (102 / 100 + 411 / 100 * αVr) * u32 * Me + 2 * η32) := by
    rw [eE]
    have := A32.filt2 (M := Me) hE hx' aE (by rw [αVr]; norm_num) (by rw [αVr]; norm_num)
      (by norm_num) (by rw [hu]; nlinarith) hdM hEM (by linarith)
    refine this.mono (le_of_eq ?_); ring
  have hE'b : |r.1._error.toReal| ≤ 2 * Me := by
    have h1 := hE'.abs_le
    have h2 : |s._error.toReal + αVr * ((target.toReal - meas.toReal) - s._error.toReal)| ≤ Me := by
      rw [show s._error.toReal + αVr * ((target.toReal - meas.toReal) - s._error.toReal) =
        (1 - αVr) * s._error.toReal + αVr * (target.toReal - meas.toReal) by ring]
      refine (abs_add_le _ _).trans ?_
      rw [abs_mul, abs_mul, abs_of_nonneg (by rw [αVr]; norm_num : (0 : ℝ) ≤ 1 - αVr),
        abs_of_nonneg (by rw [αVr]; norm_num : (0 : ℝ) ≤ αVr)]
      have := mul_le_mul_of_nonneg_left hEM (by rw [αVr]; norm_num : (0 : ℝ) ≤ 1 - αVr)
      have := mul_le_mul_of_nonneg_left hdM (by rw [αVr]; norm_num : (0 : ℝ) ≤ αVr)
      linarith
    rw [hu] at h1
    have h3 : αVr * (1 / 16777216 * Me + η32) + (102 / 100 + 411 / 100 * αVr) * (1 / 16777216) * Me +
        2 * η32 ≤ Me := by rw [αVr]; nlinarith
    linarith
  -- the derivative filter
  obtain ⟨hD'f, hD'b⟩ := deriv_step hD hE hE'.1 hdtf hdtv aD (by rw [αVr]; norm_num)
    (by rw [αVr]; norm_num) (by norm_num) hDM (by linarith) (by linarith)
  rw [← eD] at hD'f hD'b
  -- the output
  have hP := (A32.of_exact hE'.1).mul ((A32.of_exact hkp).congr hkpv) (by
    simp only [mul_zero, zero_mul, add_zero, abs_zero]; rw [abs_mul]; norm_num [capF]; nlinarith)
  simp only [mul_zero, zero_mul, add_zero, abs_zero, zero_add] at hP
  have hI0 : r.1._integrator.IsFinite ∧ r.1._integrator.toReal = 0 := by
    rw [eI]; exact ⟨Float32.isFinite_lit_zero, Float32.toReal_lit_zero⟩
  obtain ⟨s1f, s1v⟩ := f32_add_zero hP.1 hI0.1 hI0.2
  obtain ⟨q1f, q1v⟩ := f32_mul_zero hD'f hkd hkdv
  obtain ⟨s2f, s2v⟩ := f32_add_zero s1f q1f q1v
  have hTf : r.1._target.IsFinite := by rw [eT]; exact ht
  obtain ⟨q2f, q2v⟩ := f32_mul_zero hTf hkff hkffv
  obtain ⟨s3f, s3v⟩ := f32_add_zero s2f q2f q2v
  refine ⟨hE', ⟨eO ▸ s3f, ?_⟩, eR, hD'f, hD'b, hE'b, eI⟩
  rw [eO, s3v, s2v, s1v, mul_comm (5 : ℝ)]
  refine hP.2.trans ?_
  rw [abs_mul, show |(5 : ℝ)| = 5 by norm_num, hu]
  nlinarith [abs_nonneg r.1._error.toReal]

end PID2

end

end Contracts.Track.CtrlV
