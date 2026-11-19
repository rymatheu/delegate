import Contracts.Track.CtrlHorizontalBase

/-!
# C-series, `AC_PID_2D::update_all` of the horizontal velocity loop (milestone M6)

`AC_PosControl::NE_update_controller` calls `_pid_vel_ne_m.update_all(vel_target, vel_estimate,
_dt_s, _limit_vector_ned.xy())` (`AC_PID_2D.cpp:70-120`). This file reads the translated
`AC_PID_2D.update_all_Vector2f2_float_Vector2f` per axis as the real rows of
`Contracts.Track.Horizontal.tick` plus an explicit rounding budget, with the mission's gains
(`PSC_NE_VEL_P = 6`, `I = 1`, `D = 0.5`, `FF = 0`, `IMAX = 10`), the loop period
`dt = 0.0025f = dtf` and the filter coefficient `αE = 4886901 / 2²⁶` of both filters
(`FLTE = FLTD = 5`), all as hypotheses on the fields:

* `update_all_eq`: the result as explicit `float` expressions (the filter branch: no reset, finite
  inputs, `dt > 0`);
* `update_i_zero`: with the limit vector zero (`limit_accel_xy` inactive on the previous tick) and
  the new integrator inside `IMAX`, `update_i` is `I + (E⁺ · ki) · dt`, unclamped;
* `rowE`, `rowD`, `rowI`, `rowOut`: one axis, against the ideal law, with the region
  `|target|, |meas|, |E| ≤ 4`, `|D| ≤ 64`, `|I| ≤ 9`;
* `pid_spec`: the two together on both axes. Per axis (`E, D, I` the state before, `E⁺, D⁺, I⁺` the
  `float` values after, `t` the target, `m` the measurement):
  - `⟦E⁺⟧ = E + αE ((t - m) - E) + β`, `|β| ≤ 5·10⁻⁷`;
  - `⟦D⁺⟧ = D + αE ((⟦E⁺⟧ - E)/dtf - D) + β`, `|β| ≤ 2·10⁻⁵`;
  - `⟦I⁺⟧ = I + ki dtf ⟦E⁺⟧ + β`, `|β| ≤ 6·10⁻⁷`;
  - `⟦out⟧ = kp ⟦E⁺⟧ + ⟦I⁺⟧ + kd ⟦D⁺⟧ + β`, `|β| ≤ 1.5·10⁻⁵`.
-/

namespace Contracts.Track.HCtl

open AC_PosControl_lib Contracts.Quick Contracts.Mission Float.Model UnpackedFloat
open Contracts.Track.Horizontal (αE dtf)

noncomputable section

/-! ## The structure of `update_all` -/

section
variable (p : AC_PID_2D.Params) (s : AC_PID_2D.State) (dt : Float32) (lim : Vector2f.State)
theorem ui_error : (AC_PID_2D.update_i p s dt lim)._error = s._error := by
  unfold AC_PID_2D.update_i; simp only [Id.run]; split <;> (try split) <;> rfl
theorem ui_derivative : (AC_PID_2D.update_i p s dt lim)._derivative = s._derivative := by
  unfold AC_PID_2D.update_i; simp only [Id.run]; split <;> (try split) <;> rfl
theorem ui_target : (AC_PID_2D.update_i p s dt lim)._target = s._target := by
  unfold AC_PID_2D.update_i; simp only [Id.run]; split <;> (try split) <;> rfl
theorem ui_reset : (AC_PID_2D.update_i p s dt lim)._reset_filter = s._reset_filter := by
  unfold AC_PID_2D.update_i; simp only [Id.run]; split <;> (try split) <;> rfl
end

/-- The new error filter state, `E + ((t - m) - E) · α` per axis. -/
def newE (p : AC_PID_2D.Params) (s : AC_PID_2D.State) (tg m : Vector2f.State) (dt : Float32) :
    Vector2f.State :=
  { x := s._error.x + (tg.x - m.x - s._error.x) * AC_PID_2D.get_filt_E_alpha p dt,
    y := s._error.y + (tg.y - m.y - s._error.y) * AC_PID_2D.get_filt_E_alpha p dt }

/-- The new derivative filter state, `D + ((E⁺ - E)/dt - D) · α` per axis. -/
def newD (p : AC_PID_2D.Params) (s : AC_PID_2D.State) (tg m : Vector2f.State) (dt : Float32) :
    Vector2f.State :=
  { x := s._derivative.x + (((newE p s tg m dt).x - s._error.x) / dt - s._derivative.x) *
      AC_PID_2D.get_filt_D_alpha p dt,
    y := s._derivative.y + (((newE p s tg m dt).y - s._error.y) / dt - s._derivative.y) *
      AC_PID_2D.get_filt_D_alpha p dt }

/-- The state `update_i` receives. -/
def preI (p : AC_PID_2D.Params) (s : AC_PID_2D.State) (tg m : Vector2f.State) (dt : Float32) :
    AC_PID_2D.State :=
  { s with _target := tg, _error := newE p s tg m dt, _derivative := newD p s tg m dt,
           _reset_filter := false }

/-- **The structure of `update_all`** (the filter branch). -/
theorem update_all_eq (p : AC_PID_2D.Params) (s : AC_PID_2D.State) (tg m : Vector2f.State)
    (dt : Float32) (lim : Vector2f.State)
    (hnan : (Vector2f.is_nan tg || Vector2f.is_inf tg || Vector2f.is_nan m || Vector2f.is_inf m) = false)
    (hr : s._reset_filter = false) (hdt : is_positive_float dt = true) :
    let r := AC_PID_2D.update_all_Vector2f2_float_Vector2f p s tg m dt lim
    r.1._error = newE p s tg m dt ∧ r.1._derivative = newD p s tg m dt ∧
      r.1._reset_filter = false ∧
      r.1._integrator = (AC_PID_2D.update_i p (preI p s tg m dt) dt lim)._integrator ∧
      r.2 = { x := ((newE p s tg m dt).x * p._kp + r.1._integrator.x +
                  (newD p s tg m dt).x * p._kd + tg.x * p._kff),
              y := ((newE p s tg m dt).y * p._kp + r.1._integrator.y +
                  (newD p s tg m dt).y * p._kd + tg.y * p._kff) } := by
  intro r
  simp only [r, AC_PID_2D.update_all_Vector2f2_float_Vector2f, hnan, hr, hdt, Id.run,
    Bool.false_eq_true, ite_false, ite_true, pure, ui_error, ui_derivative, ui_target, ui_reset]
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> first | rfl | trivial

/-! ## One axis against the ideal law -/

theorem αE_val : ((αE : ℚ) : ℝ) = 4886901 / 67108864 := by norm_num [αE]
theorem dtf_val : ((dtf : ℚ) : ℝ) = 5368709 / 2147483648 := by norm_num [dtf]

/-- The error filter. -/
theorem rowE {t m E α : Float32} (ht : t.IsFinite) (hm : m.IsFinite) (hE : E.IsFinite)
    (hα : A32 α (αE : ℝ) (1 / 2 ^ 22)) (htb : |t.toReal| ≤ 4) (hmb : |m.toReal| ≤ 4)
    (hEb : |E.toReal| ≤ 4) :
    B32 (E + (t - m - E) * α) (E.toReal + (αE : ℝ) * ((t.toReal - m.toReal) - E.toReal))
      (35 / 10 ^ 7) (39 / 8) := by
  rw [αE_val] at hα ⊢
  have bt := B32.val ht htb
  have bm := B32.val hm hmb
  have bE := B32.val hE hEb
  have ba : B32 α (4886901 / 67108864) (1 / 2 ^ 22) (4886901 / 67108864) :=
    ⟨hα, by norm_num⟩
  have b1 : B32 (t - m) (t.toReal - m.toReal) (5 / 10 ^ 7) 8 :=
    B32.sub bt bm (by norm_num) (by norm_num [capF]) (by norm_num)
  have b2 : B32 (t - m - E) (t.toReal - m.toReal - E.toReal) (13 / 10 ^ 7) 12 :=
    B32.sub b1 bE (by norm_num) (by norm_num [capF]) (by norm_num)
  have b3 : B32 ((t - m - E) * α) ((t.toReal - m.toReal - E.toReal) * (4886901 / 67108864))
      (31 / 10 ^ 7) (7 / 8) :=
    B32.mul b2 ba (by norm_num [capF]) (by norm_num) (by norm_num)
  have b4 := B32.add bE b3 (e := 35 / 10 ^ 7) (R := 39 / 8) (by norm_num) (by norm_num [capF])
    (by norm_num)
  exact b4.congr (by ring)

/-- The derivative filter, against the `float` value of the new error. -/
theorem rowD {E' E D α dt : Float32} (hE' : E'.IsFinite) (hE : E.IsFinite) (hD : D.IsFinite)
    (hα : A32 α (αE : ℝ) (1 / 2 ^ 22)) (hdt : dt.IsFinite)
    (hdtv : dt.toReal = (dtf : ℝ)) (hE'b : |E'.toReal| ≤ 8) (hEb : |E.toReal| ≤ 8)
    (hdE : |E'.toReal - E.toReal| ≤ 88 / 100) (hDb : |D.toReal| ≤ 64) :
    B32 (D + ((E' - E) / dt - D) * α)
      (D.toReal + (αE : ℝ) * ((E'.toReal - E.toReal) / (dtf : ℝ) - D.toReal)) (12 / 10 ^ 5) 95 := by
  rw [αE_val] at hα ⊢
  rw [dtf_val] at hdtv ⊢
  have bE' := B32.val hE' hE'b
  have bE := B32.val hE hEb
  have bD := B32.val hD hDb
  have ba : B32 α (4886901 / 67108864) (1 / 2 ^ 22) (4886901 / 67108864) :=
    ⟨hα, by norm_num⟩
  have bdt : B32 dt (5368709 / 2147483648) 0 (5368709 / 2147483648) :=
    B32.lit hdt hdtv (by norm_num)
  have b1 : B32 (E' - E) (E'.toReal - E.toReal) (6 / 10 ^ 8) (88 / 100) :=
    B32.sub_R bE' bE hdE (by norm_num [capF]) (by norm_num)
  have b2 : B32 ((E' - E) / dt) ((E'.toReal - E.toReal) / (5368709 / 2147483648)) (5 / 10 ^ 5)
      353 :=
    B32.div (mlo := 5368709 / 2147483648) b1 bdt (by norm_num) (by norm_num) (by norm_num)
      (by norm_num [capF]) (by norm_num)
  have b3 : B32 ((E' - E) / dt - D)
      ((E'.toReal - E.toReal) / (5368709 / 2147483648) - D.toReal) (8 / 10 ^ 5) 417 :=
    B32.sub b2 bD (by norm_num) (by norm_num [capF]) (by norm_num)
  have b4 : B32 (((E' - E) / dt - D) * α)
      (((E'.toReal - E.toReal) / (5368709 / 2147483648) - D.toReal) * (4886901 / 67108864))
      (11 / 10 ^ 5) 31 :=
    B32.mul b3 ba (by norm_num [capF]) (by norm_num) (by norm_num)
  have b5 := B32.add bD b4 (e := 12 / 10 ^ 5) (R := 95) (by norm_num) (by norm_num [capF])
    (by norm_num)
  exact b5.congr (by ring)

/-- The integrator step, against the `float` value of the new error. -/
theorem rowI {E' I ki dt : Float32} (hE' : E'.IsFinite) (hI : I.IsFinite) (hki : ki.IsFinite)
    (hkiv : ki.toReal = 1) (hdt : dt.IsFinite) (hdtv : dt.toReal = (dtf : ℝ))
    (hE'b : |E'.toReal| ≤ 5) (hIb : |I.toReal| ≤ 9) :
    B32 (I + E' * ki * dt) (I.toReal + 1 * (dtf : ℝ) * E'.toReal) (6 / 10 ^ 7) (9 + 1 / 80) := by
  rw [dtf_val] at hdtv ⊢
  have bE' : B32 (E' * ki) E'.toReal 0 5 := B32.mul_one (B32.val hE' hE'b) hki hkiv
  have bI := B32.val hI hIb
  have bdt : B32 dt (5368709 / 2147483648) 0 (5368709 / 2147483648) :=
    B32.lit hdt hdtv (by norm_num)
  have b1 : B32 (E' * ki * dt) (E'.toReal * (5368709 / 2147483648)) (1 / 10 ^ 9) (1 / 80) :=
    B32.mul bE' bdt (by norm_num [capF]) (by norm_num) (by norm_num)
  have b2 := B32.add bI b1 (e := 6 / 10 ^ 7) (R := 9 + 1 / 80) (by norm_num) (by norm_num [capF])
    (by norm_num)
  exact b2.congr (by ring)

/-- The output `E⁺ kp + I⁺ + D⁺ kd + t kff` with `kff = 0`, against the `float` values. -/
theorem rowOut {E' I' D' t kp kd kff : Float32} (hE' : E'.IsFinite) (hI' : I'.IsFinite)
    (hD' : D'.IsFinite) (ht : t.IsFinite) (hkp : kp.IsFinite) (hkpv : kp.toReal = 6)
    (hkd : kd.IsFinite) (hkdv : kd.toReal = 1 / 2) (hkff : kff.IsFinite) (hkffv : kff.toReal = 0)
    (hE'b : |E'.toReal| ≤ 5) (hI'b : |I'.toReal| ≤ 10) (hD'b : |D'.toReal| ≤ 96) :
    B32 (E' * kp + I' + D' * kd + t * kff) (6 * E'.toReal + I'.toReal + 1 / 2 * D'.toReal)
      (3 / 2 / 10 ^ 5) 88 := by
  have bE' := B32.val hE' hE'b
  have bI' := B32.val hI' hI'b
  have bD' := B32.val hD' hD'b
  have bkp : B32 kp 6 0 6 := B32.lit hkp hkpv (by norm_num)
  have bkd : B32 kd (1 / 2) 0 (1 / 2) := B32.lit hkd hkdv (by norm_num)
  have o1 : B32 (E' * kp) (E'.toReal * 6) (2 / 10 ^ 6) 30 :=
    B32.mul bE' bkp (by norm_num [capF]) (by norm_num) (by norm_num)
  have o2 : B32 (E' * kp + I') (E'.toReal * 6 + I'.toReal) (5 / 10 ^ 6) 40 :=
    B32.add o1 bI' (by norm_num) (by norm_num [capF]) (by norm_num)
  have o3 : B32 (D' * kd) (D'.toReal * (1 / 2)) (3 / 10 ^ 6) 48 :=
    B32.mul bD' bkd (by norm_num [capF]) (by norm_num) (by norm_num)
  have o4 : B32 (E' * kp + I' + D' * kd) (E'.toReal * 6 + I'.toReal + D'.toReal * (1 / 2))
      (3 / 2 / 10 ^ 5) 88 :=
    B32.add o2 o3 (by norm_num) (by norm_num [capF]) (by norm_num)
  have hz := Float32.mul_zero_val ht hkff hkffv
  exact (B32.add_zero o4 hz.1 hz.2).congr (by ring)

/-! ## `update_i` with the limit vector zero -/

/-- **`update_i` with a zero limit vector**: the step is added unclamped when the new integrator
is inside `IMAX` (`limit_length` inactive). -/
theorem update_i_zero (p : AC_PID_2D.Params) (s : AC_PID_2D.State) (dt : Float32)
    (lim : Vector2f.State) (hlx : lim.x.IsFinite) (hlx0 : lim.x.toReal = 0)
    (hly : lim.y.IsFinite) (hly0 : lim.y.toReal = 0)
    (hdx : (s._error.x * p._ki * dt).IsFinite) (hdy : (s._error.y * p._ki * dt).IsFinite)
    (hix : (s._integrator.x + s._error.x * p._ki * dt).IsFinite)
    (hiy : (s._integrator.y + s._error.y * p._ki * dt).IsFinite)
    (hix' : |(s._integrator.x + s._error.x * p._ki * dt).toReal| ≤ 2 ^ 40)
    (hiy' : |(s._integrator.y + s._error.y * p._ki * dt).toReal| ≤ 2 ^ 40)
    (hk : p._kimax.IsFinite)
    (hlen : N2 (s._integrator.x + s._error.x * p._ki * dt).toReal
        (s._integrator.y + s._error.y * p._ki * dt).toReal * (1 + 1 / 2 ^ 22) + 1 / 2 ^ 70 ≤
      p._kimax.toReal) :
    (AC_PID_2D.update_i p s dt lim)._integrator =
      { x := s._integrator.x + s._error.x * p._ki * dt,
        y := s._integrator.y + s._error.y * p._ki * dt } := by
  rw [Contracts.Track.TwoD.update_i_integrator]
  have hpos : is_positive_float (Vector2f.op_mul_Vector2f
      (Vector2f.op_mul_float (Vector2f.op_mul_float s._error p._ki) dt) lim) = false := by
    have h1 := Float32.mul_zero_val hdx hlx hlx0
    have h2 := Float32.mul_zero_val hdy hly hly0
    have h3 := Float32.add_zero_val h1.1 h2.1 h2.2
    rcases hz : is_positive_float (Vector2f.op_mul_Vector2f
      (Vector2f.op_mul_float (Vector2f.op_mul_float s._error p._ki) dt) lim) with _ | _
    · rfl
    · have h4 := (isPos_iff h3.1).1 hz
      rw [h3.2, h1.2] at h4
      exact absurd h4 (by norm_num)
  rw [ite_eq_right (by rw [hpos]; decide)]
  have hv : (Vector2f.op_add_assign s._integrator
      (Vector2f.op_mul_float (Vector2f.op_mul_float s._error p._ki) dt)).1 =
      { x := s._integrator.x + s._error.x * p._ki * dt,
        y := s._integrator.y + s._error.y * p._ki * dt } := rfl
  rw [hv, limit_length_inactive { x := s._integrator.x + s._error.x * p._ki * dt, y := s._integrator.y + s._error.y * p._ki * dt } p._kimax hix hiy hix' hiy' hk hlen]

/-! ## The velocity PID on the region -/

/-- The gains, the period and the filter coefficients of `_pid_vel_ne_m` (the mission's values). -/
structure VelGains (q : AC_PID_2D.Params) (dt : Float32) : Prop where
  kp : q._kp.IsFinite ∧ q._kp.toReal = 6
  ki : q._ki.IsFinite ∧ q._ki.toReal = 1
  kd : q._kd.IsFinite ∧ q._kd.toReal = 1 / 2
  kff : q._kff.IsFinite ∧ q._kff.toReal = 0
  kimax : q._kimax.IsFinite ∧ q._kimax.toReal = 10
  hdt : dt.IsFinite ∧ dt.toReal = (dtf : ℝ)
  fE : q._filt_E_hz.IsFinite ∧ q._filt_E_hz.toReal = 5
  fD : q._filt_D_hz.IsFinite ∧ q._filt_D_hz.toReal = 5

/-- A finite `float` of value at most `B` in magnitude. -/
def FB (B : ℝ) (x : Float32) : Prop := x.IsFinite ∧ |x.toReal| ≤ B

/-- The region of one tick of the velocity PID: the filter branch, finite inputs and state within
the bounds, the integrator inside `9 < IMAX`, the limit vector zero. -/
structure VelRegion (s : AC_PID_2D.State) (tg m lim : Vector2f.State) : Prop where
  reset : s._reset_filter = false
  tx : FB 4 tg.x
  ty : FB 4 tg.y
  mx : FB 4 m.x
  my : FB 4 m.y
  Ex : FB 4 s._error.x
  Ey : FB 4 s._error.y
  Dx : FB 64 s._derivative.x
  Dy : FB 64 s._derivative.y
  Ix : s._integrator.x.IsFinite
  Iy : s._integrator.y.IsFinite
  I9 : N2 s._integrator.x.toReal s._integrator.y.toReal ≤ 9
  limx : lim.x.IsFinite ∧ lim.x.toReal = 0
  limy : lim.y.IsFinite ∧ lim.y.toReal = 0

/-- **One axis of the velocity PID** (`HORIZONTAL.md` §7): the new error, derivative and
integrator and the output, each the real row of `Horizontal.tick` on the `float` values of its
inputs, within an explicit bound; with the magnitudes the next stage needs. -/
def PIDAxis (t m E D I : ℝ) (E' D' I' out : Float32) : Prop :=
  A32 E' (E + (αE : ℝ) * ((t - m) - E)) (35 / 10 ^ 7) ∧
  A32 D' (D + (αE : ℝ) * ((E'.toReal - E) / (dtf : ℝ) - D)) (12 / 10 ^ 5) ∧
  A32 I' (I + (Horizontal.ki : ℝ) * (dtf : ℝ) * E'.toReal) (6 / 10 ^ 7) ∧
  A32 out ((Horizontal.kp : ℝ) * E'.toReal + I'.toReal + (Horizontal.kd : ℝ) * D'.toReal)
    (3 / 2 / 10 ^ 5) ∧
  |E'.toReal| ≤ 5 ∧ |D'.toReal| ≤ 96 ∧ |I'.toReal| ≤ 10 ∧ |out.toReal| ≤ 89

theorem αE_le : ((αE : ℚ) : ℝ) ≤ 1 / 10 := by norm_num [αE]
theorem dtf_pos : (0 : ℝ) < ((dtf : ℚ) : ℝ) := by norm_num [dtf]

/-- One axis: the float facts `PIDAxis` from the row lemmas. -/
theorem pid_axis {t m E D I α αd dt ki kp kd kff : Float32} (ht : FB 4 t) (hm : FB 4 m)
    (hE : FB 4 E) (hD : FB 64 D) (hI : I.IsFinite) (hIb : |I.toReal| ≤ 9)
    (hα : A32 α (αE : ℝ) (1 / 2 ^ 22)) (hαd : A32 αd (αE : ℝ) (1 / 2 ^ 22))
    (hdt : dt.IsFinite) (hdtv : dt.toReal = (dtf : ℝ)) (hki : ki.IsFinite) (hkiv : ki.toReal = 1)
    (hkp : kp.IsFinite) (hkpv : kp.toReal = 6) (hkd : kd.IsFinite) (hkdv : kd.toReal = 1 / 2)
    (hkff : kff.IsFinite) (hkffv : kff.toReal = 0) :
    let E' := E + (t - m - E) * α
    let D' := D + ((E' - E) / dt - D) * αd
    let I' := I + E' * ki * dt
    PIDAxis t.toReal m.toReal E.toReal D.toReal I.toReal E' D' I' (E' * kp + I' + D' * kd + t * kff) := by
  intro E' D' I'
  simp only [E', D', I']
  have bE := rowE ht.1 hm.1 hE.1 hα ht.2 hm.2 hE.2
  have hE'b : |E'.toReal| ≤ 5 := by
    have := A32.abs_le' bE.1; have := bE.2; linarith
  have hdE : |E'.toReal - E.toReal| ≤ 88 / 100 := by
    have h1 := bE.1.2
    have h2 : |(αE : ℝ) * ((t.toReal - m.toReal) - E.toReal)| ≤ 875 / 1000 := by
      rw [abs_mul, abs_of_pos (by norm_num [αE])]
      have : |t.toReal - m.toReal - E.toReal| ≤ 12 := by
        have := abs_sub (t.toReal - m.toReal) E.toReal
        have := abs_sub t.toReal m.toReal
        linarith [ht.2, hm.2, hE.2]
      have h3 : (0 : ℝ) ≤ (αE : ℝ) := by norm_num [αE]
      calc (αE : ℝ) * |t.toReal - m.toReal - E.toReal| ≤ (αE : ℝ) * 12 :=
            mul_le_mul_of_nonneg_left this h3
        _ ≤ 875 / 1000 := by norm_num [αE]
    calc |E'.toReal - E.toReal| ≤ |E'.toReal - (E.toReal + (αE : ℝ) *
          ((t.toReal - m.toReal) - E.toReal))| + |(αE : ℝ) * ((t.toReal - m.toReal) - E.toReal)| := by
          have := abs_sub_le E'.toReal (E.toReal + (αE : ℝ) * ((t.toReal - m.toReal) - E.toReal))
            E.toReal
          simpa using this
      _ ≤ 35 / 10 ^ 7 + 875 / 1000 := add_le_add h1 h2
      _ ≤ 88 / 100 := by norm_num
  have bD := rowD bE.1.1 hE.1 hD.1 hαd hdt hdtv (hE'b.trans (by norm_num))
    (hE.2.trans (by norm_num)) hdE hD.2
  have hD'b : |D'.toReal| ≤ 96 := by
    have := A32.abs_le' bD.1; have := bD.2; linarith
  have bI := rowI bE.1.1 hI hki hkiv hdt hdtv hE'b hIb
  have hI'b : |I'.toReal| ≤ 10 := by
    have := A32.abs_le' bI.1; have := bI.2; linarith
  have bO := rowOut bE.1.1 bI.1.1 bD.1.1 ht.1 hkp hkpv hkd hkdv hkff hkffv hE'b hI'b hD'b
  have hOb : |(E' * kp + I' + D' * kd + t * kff).toReal| ≤ 89 := by
    have := A32.abs_le' bO.1; have := bO.2; linarith
  refine ⟨bE.1, bD.1, ?_, ?_, hE'b, hD'b, hI'b, hOb⟩
  · exact bI.1.congr (by norm_num [Horizontal.ki])
  · exact bO.1.congr (by norm_num [Horizontal.kp, Horizontal.kd])

theorem step_fin {E ki dt : Float32} (hE : |E.toReal| ≤ 5) (hki : ki.IsFinite)
    (hkiv : ki.toReal = 1) (hdt : dt.IsFinite) (hdtv : dt.toReal = (dtf : ℝ)) (hEf : E.IsFinite) :
    (E * ki * dt).IsFinite := by
  rw [dtf_val] at hdtv
  have bE' : B32 (E * ki) E.toReal 0 5 := B32.mul_one (B32.val hEf hE) hki hkiv
  have bdt : B32 dt (5368709 / 2147483648) 0 (5368709 / 2147483648) :=
    B32.lit hdt hdtv (by norm_num)
  exact (B32.mul bE' bdt (e := 1 / 10 ^ 9) (R := 1 / 80) (by norm_num [capF]) (by norm_num)
    (by norm_num)).1.1

theorem dt_isPos {dt : Float32} (hdt : dt.IsFinite) (hdtv : dt.toReal = (dtf : ℝ)) :
    is_positive_float dt = true :=
  (isPos_iff hdt).2 (by rw [hdtv]; norm_num [dtf])

set_option maxHeartbeats 1000000 in
/-- **C-series, the velocity PID** (`AC_PID_2D::update_all`, the mission's gains, on the region):
both axes are `PIDAxis` of the inputs, the filter states are the explicit `newE`, `newD`, the
integrator is `I + (E⁺ ki) dt` unclamped and `_reset_filter` stays `false`. -/
theorem pid_spec (hL : LibmSpec) (q : AC_PID_2D.Params) (s : AC_PID_2D.State) (tg m lim : Vector2f.State)
    (dt : Float32) (g : VelGains q dt) (hR : VelRegion s tg m lim) :
    let r := AC_PID_2D.update_all_Vector2f2_float_Vector2f q s tg m dt lim
    r.1._error = newE q s tg m dt ∧ r.1._derivative = newD q s tg m dt ∧
      r.1._reset_filter = false ∧
      PIDAxis tg.x.toReal m.x.toReal s._error.x.toReal s._derivative.x.toReal
        s._integrator.x.toReal r.1._error.x r.1._derivative.x r.1._integrator.x r.2.x ∧
      PIDAxis tg.y.toReal m.y.toReal s._error.y.toReal s._derivative.y.toReal
        s._integrator.y.toReal r.1._error.y r.1._derivative.y r.1._integrator.y r.2.y := by
  intro r
  obtain ⟨h1, h2, h3, h4, h5⟩ := update_all_eq q s tg m dt lim
    (vec_ok hR.tx.1 hR.ty.1 hR.mx.1 hR.my.1) hR.reset (dt_isPos g.hdt.1 g.hdt.2)
  have hIx9 : |s._integrator.x.toReal| ≤ 9 := ((abs_le_N2 _ _).1).trans hR.I9
  have hIy9 : |s._integrator.y.toReal| ≤ 9 := ((abs_le_N2 _ _).2).trans hR.I9
  have hdt' : dt.toReal = 5368709 / 2147483648 := by rw [g.hdt.2, dtf_val]
  have aE : A32 (AC_PID_2D.get_filt_E_alpha q dt) (αE : ℝ) (1 / 2 ^ 22) := by
    rw [αE_val]; exact alpha5 hL g.hdt.1 hdt' g.fE.1 g.fE.2
  have aD : A32 (AC_PID_2D.get_filt_D_alpha q dt) (αE : ℝ) (1 / 2 ^ 22) := by
    rw [αE_val]; exact alpha5 hL g.hdt.1 hdt' g.fD.1 g.fD.2
  have ax := pid_axis hR.tx hR.mx hR.Ex hR.Dx hR.Ix hIx9 aE aD g.hdt.1 g.hdt.2
    g.ki.1 g.ki.2 g.kp.1 g.kp.2 g.kd.1 g.kd.2 g.kff.1 g.kff.2
  have ay := pid_axis hR.ty hR.my hR.Ey hR.Dy hR.Iy hIy9 aE aD g.hdt.1 g.hdt.2
    g.ki.1 g.ki.2 g.kp.1 g.kp.2 g.kd.1 g.kd.2 g.kff.1 g.kff.2
  have sx : ((newE q s tg m dt).x * q._ki * dt).IsFinite := step_fin ax.2.2.2.2.1 g.ki.1 g.ki.2 g.hdt.1 g.hdt.2 ax.1.1
  have sy : ((newE q s tg m dt).y * q._ki * dt).IsFinite := step_fin ay.2.2.2.2.1 g.ki.1 g.ki.2 g.hdt.1 g.hdt.2 ay.1.1
  have hInt : r.1._integrator =
      { x := s._integrator.x + (newE q s tg m dt).x * q._ki * dt,
        y := s._integrator.y + (newE q s tg m dt).y * q._ki * dt } := by
    rw [h4]
    obtain ⟨-, -, aIx, -, hE'x, -, hI'x, -⟩ := ax
    obtain ⟨-, -, aIy, -, hE'y, -, hI'y, -⟩ := ay
    have hl : N2 (s._integrator.x + (newE q s tg m dt).x * q._ki * dt).toReal
        (s._integrator.y + (newE q s tg m dt).y * q._ki * dt).toReal ≤ 9 + 1 / 30 := by
      refine (N2_le_near _ _ s._integrator.x.toReal s._integrator.y.toReal).trans ?_
      have ex := aIx.2
      have ey := aIy.2
      have kx : |(Horizontal.ki : ℝ) * (dtf : ℝ) * (newE q s tg m dt).x.toReal| ≤ 1 / 79 := by
        rw [abs_mul, abs_mul]
        have : |(Horizontal.ki : ℝ)| * |(dtf : ℝ)| ≤ 1 / 395 := by norm_num [Horizontal.ki, dtf]
        have h0 : 0 ≤ |(Horizontal.ki : ℝ)| * |(dtf : ℝ)| := by positivity
        calc |(Horizontal.ki : ℝ)| * |(dtf : ℝ)| * |(newE q s tg m dt).x.toReal|
            ≤ 1 / 395 * 5 := mul_le_mul this hE'x (abs_nonneg _) (by norm_num)
          _ ≤ 1 / 79 := by norm_num
      have ky : |(Horizontal.ki : ℝ) * (dtf : ℝ) * (newE q s tg m dt).y.toReal| ≤ 1 / 79 := by
        rw [abs_mul, abs_mul]
        have : |(Horizontal.ki : ℝ)| * |(dtf : ℝ)| ≤ 1 / 395 := by norm_num [Horizontal.ki, dtf]
        calc |(Horizontal.ki : ℝ)| * |(dtf : ℝ)| * |(newE q s tg m dt).y.toReal|
            ≤ 1 / 395 * 5 := mul_le_mul this hE'y (abs_nonneg _) (by norm_num)
          _ ≤ 1 / 79 := by norm_num
      have dx : |(s._integrator.x + (newE q s tg m dt).x * q._ki * dt).toReal -
          s._integrator.x.toReal| ≤ 6 / 10 ^ 7 + 1 / 79 := by
        have := abs_sub_le (s._integrator.x + (newE q s tg m dt).x * q._ki * dt).toReal
          (s._integrator.x.toReal + (Horizontal.ki : ℝ) * (dtf : ℝ) * (newE q s tg m dt).x.toReal)
          s._integrator.x.toReal
        rw [add_sub_cancel_left] at this
        exact this.trans (add_le_add ex kx)
      have dy : |(s._integrator.y + (newE q s tg m dt).y * q._ki * dt).toReal -
          s._integrator.y.toReal| ≤ 6 / 10 ^ 7 + 1 / 79 := by
        have := abs_sub_le (s._integrator.y + (newE q s tg m dt).y * q._ki * dt).toReal
          (s._integrator.y.toReal + (Horizontal.ki : ℝ) * (dtf : ℝ) * (newE q s tg m dt).y.toReal)
          s._integrator.y.toReal
        rw [add_sub_cancel_left] at this
        exact this.trans (add_le_add ey ky)
      have := hR.I9
      linarith
    have hlen : N2 (s._integrator.x + (newE q s tg m dt).x * q._ki * dt).toReal
        (s._integrator.y + (newE q s tg m dt).y * q._ki * dt).toReal * (1 + 1 / 2 ^ 22) +
          1 / 2 ^ 70 ≤ q._kimax.toReal := by
      rw [g.kimax.2]
      have hN := N2_nonneg (s._integrator.x + (newE q s tg m dt).x * q._ki * dt).toReal
        (s._integrator.y + (newE q s tg m dt).y * q._ki * dt).toReal
      nlinarith
    exact update_i_zero q (preI q s tg m dt) dt lim hR.limx.1 hR.limx.2 hR.limy.1 hR.limy.2
      sx sy aIx.1 aIy.1 (hI'x.trans (by norm_num)) (hI'y.trans (by norm_num)) g.kimax.1 hlen
  refine ⟨h1, h2, h3, ?_, ?_⟩
  · rw [h5]
    dsimp only
    rw [hInt, h1, h2]
    exact ax
  · rw [h5]
    dsimp only
    rw [hInt, h1, h2]
    exact ay

end

end Contracts.Track.HCtl
