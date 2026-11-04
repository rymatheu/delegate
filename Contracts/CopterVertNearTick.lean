import Contracts.CopterVertNearStep
import Contracts.CopterPlant

/-!
# One tick of the vertical channel: the `Float32` code follows `CopterVert.stepN`

The per-function lemmas of `Contracts.CopterVertNearStep` composed in the order of one 400 Hz tick
(`Copter.loop`): the motors filter the stored throttle (`update_throttle_filter`, then the mixer and
`output_to_motors`), the position P controller, the velocity PID, the acceleration measurement, the
acceleration PID, the hover offset and `set_throttle_out`, wired as `D_update_controller` wires them
(the velocity target `· get_control_gain_scaler_Z() + (desired + offset + terrain)`, the same for
the acceleration target). The plant moves with the new actuator.

**The real state is read off the floats.** `vx` takes the exact values of the stored floats: the
velocity error filter, the acceleration error filter, the integrator minus `I* = H - 4/9`, the
throttle filter minus `4/9`, and the plant's `ζ = z + 1`, `w`. The perturbations of `stepN` are then
defined as the differences, and `vert_tick` bounds them by `NBound`: nothing accumulates between
ticks except through `stepN` itself.

**The tick invariant** (`VInv`, section 10 of `staging/text/vertical-channel.md`): the PIDs are out of
reset; the dead states (the velocity derivative filter, the acceleration target and derivative
filters) are finite and bounded; the throttle filter's cutoff is 2 Hz; and **the stored throttle**
`_throttle_in` is within `3.7 · 10⁻⁸` of `4/9 - kp Ea - ι`, with `Ea`, `ι` the exact values of the
stored acceleration error filter and integrator. `vert_tick` re-establishes it.

**What the tick takes as hypotheses** (the zero half, the navigator, the C library, the plumbing):
the position target is exactly `-1` and the position error limits and `D1_max` are at least `1 cm`;
the gain scaler is `1` and the feed-forward sums are zeros; `cos pitch = cos roll = 1` and
`cos(_thrust_angle_rad) = 1`; `MOT_THST_HOVER = 0.4444`; the motors' period is `dtF`; and the mixer
`output_armed_stabilizing` puts the throttle filter output on the four `_thrust_rpyt_out`
(`MixerPass`; with zero roll, pitch and yaw inputs this is `CopterZeroMotors.output_armed_stabilizing_Z`
of the zero half, not imported here). The narrowing `(float)` is `NarrowSpec`, the sensors are
`CopterSense`.

**Not here** (the gap to a closed-loop statement over `Copter.loop`): that the state reached by
`Copter.loop` at a hover sample has its vertical path equal to the composition below. This needs the
navigator lemma (`AC_WPNav.update_wpnav` keeps `_pos_desired.z = -1`, zero velocity and acceleration
feed-forward, and the offsets and terrain terms zero, `D_update_offsets`/`update_terrain` at zero),
`update_estimates` (the position and velocity estimates are the sample's), the zero half (zero
`rpy` inputs, hence `MixerPass`, level attitude so `cos = 1`), and the unfolding of
`D_update_controller`, `ModeAuto.run`, `Copter.loop` and `AP_MotorsMatrix.output` into these calls,
plus the first tick (`D_init_controller`, section 10 step 5 of the notes).
-/

open Float.Model UnpackedFloat AP_Math Contracts.CopterVert

namespace Contracts.CopterVertNear

noncomputable section

attribute [local irreducible] av aa am kp ki kv kpos dtc g k CopterVert.h Gf Hf

/-! ## Sensing -/

/-- The sensor readings of a vertical state at the hover, from `CopterSense`: position within
`10⁻¹⁵` (binary64), velocity within `6 · 10⁻¹⁰`, specific force within `6 · 10⁻⁷`. -/
theorem sense_near {sense32 : ℝ → Float32} {senseP : ℝ → Float}
    (hS : CopterPlant.CopterSense sense32 senseP) {ζ w f : ℝ} (hζ : |ζ| ≤ 1 / 200)
    (hw : |w| ≤ 1 / 100) (hf : |f| ≤ 10.05) :
    Near64 (senseP (ζ - 1)) (ζ - 1) 1e-15 ∧ Near32 (sense32 w) w 6e-10 ∧
      Near32 (sense32 f) f 6e-7 := by
  have hζ' := abs_le.1 hζ
  have hz : |ζ - 1| ≤ 1.005 := by apply bnd <;> linarith
  obtain ⟨p1, p2⟩ := hS.pos.err (ζ - 1) (by linarith)
  obtain ⟨w1, w2⟩ := hS.f32.err w (by linarith)
  obtain ⟨f1, f2⟩ := hS.f32.err f (by linarith)
  have e53 : (2 : ℝ) ^ (-53 : ℤ) ≤ 1.2e-16 := by norm_num
  have e1075 : (2 : ℝ) ^ (-1075 : ℤ) ≤ 2 ^ (-53 : ℤ) := zpow_le_zpow_right₀ one_le_two (by norm_num)
  have e24 : (2 : ℝ) ^ (-24 : ℤ) ≤ 5.9605e-8 := by norm_num
  have e150 : (2 : ℝ) ^ (-150 : ℤ) ≤ 1e-44 := by norm_num
  have m1 := mul_le_mul e53 hz (abs_nonneg _) (by norm_num)
  have m2 := mul_le_mul e24 hw (abs_nonneg _) (by norm_num)
  have m3 := mul_le_mul e24 hf (abs_nonneg _) (by norm_num)
  refine ⟨⟨p1, p2.trans ((add_le_add m1 (e1075.trans e53)).trans (by norm_num))⟩,
    ⟨w1, w2.trans ((add_le_add m2 e150).trans (by norm_num))⟩,
    ⟨f1, f2.trans ((add_le_add m3 e150).trans (by norm_num))⟩⟩

/-! ## The plant on the vertical, in the coordinates of `CopterVert` -/

/-- Four actuators of value `4/9 + φ'` move the vertical state as the `ζ`, `w` rows of `stepN`:
`z' = z + h w`, `w' = w - k h φ'`, and the specific force is `-k (4/9 + φ')`. -/
theorem plant_vert (z w f : ℝ) (a : Vector Float32 4) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (ha : ∀ i : Fin 4, (a[i]).toReal = c) :
    CopterPlant.dyn (CopterPlant.vstate z w f) a =
      CopterPlant.vstate (z + CopterVert.h * w) (w - k * CopterVert.h * (c - 4 / 9)) (-(k * c)) := by
  rw [CopterPlant.dyn_vert z w f c a hc0 hc1 ha]
  have hh : CopterPlant.h = CopterVert.h := by rw [CopterPlant.h, h_eq]
  rw [hh]
  congr 1
  · rw [k_eq, QuadPlant.thrust2weight, CopterPlant.gravity]; ring
  · rw [k_eq, QuadPlant.thrust2weight, CopterPlant.gravity]; norm_num

/-! ## The tick -/

/-- The real vertical state read off the floats (header). -/
def vx (ζ w : ℝ) (Ev Ea I F : Float32) : VX :=
  ⟨ζ, w, Ev.toReal, Ea.toReal, I.toReal - Istar, F.toReal - 4 / 9⟩

/-- The tick invariant of the vertical floats (header). -/
-- <<VInv>>
structure VInv (sv : AC_PID_Basic.State) (sa : AC_PID.State) (m : AP_MotorsMulticopter.State) :
    Prop where
  v_reset : sv._reset_filter = false
  v_err : sv._error.IsFinite
  v_der : sv._derivative.IsFinite
  v_der_b : |sv._derivative.toReal| ≤ 3
  a_reset : sa._flags._reset_filter = false
  a_tgt : sa._target.IsFinite
  a_tgt_b : |sa._target.toReal| ≤ 3 / 10
  a_err : sa._error.IsFinite
  a_int : sa._integrator.IsFinite
  a_der : sa._derivative.IsFinite
  a_der_b : |sa._derivative.toReal| ≤ 250
  F_fin : m._throttle_filter_value.IsFinite
  cutoff : m._throttle_filter_cutoff = AC_PosControl.POSCONTROL_THROTTLE_CUTOFF_FREQ_HZ
  throttle : Near32 m._throttle_in
    (4 / 9 + (-(kp * sa._error.toReal) - (sa._integrator.toReal - Istar))) 3.7e-8
-- <</VInv>>

/-- The mixer puts the throttle filter output on the four thrusts (the zero half's lemma with
zero `rpy` inputs). -/
def MixerPass (p : AP_MotorsMulticopter.Params) (s : AP_MotorsMatrix.State) : Prop :=
  ∀ i : Fin 4, ((AP_MotorsMatrix.output_armed_stabilizing p s)._thrust_rpyt_out[i]).IsFinite ∧
    ((AP_MotorsMatrix.output_armed_stabilizing p s)._thrust_rpyt_out[i]).toReal =
      s._throttle_filter_value.toReal

/-- **The motors' half of the tick.** The new throttle filter output is within `2.9 · 10⁻⁸` of the
`φ'` line of `stepN` (as `4/9 + φ'`), and, if the mixer passes it through, the four actuators of
`output_to_motors` have its value. -/
theorem motors_tick {m : AP_MotorsMulticopter.State} {Ea ι φ : ℝ}
    (hc : m._throttle_filter_cutoff = AC_PosControl.POSCONTROL_THROTTLE_CUTOFF_FREQ_HZ)
    (hdt : m._dt_s = dtF) (hF : m._throttle_filter_value.IsFinite)
    (hφv : m._throttle_filter_value.toReal = 4 / 9 + φ)
    (hT : Near32 m._throttle_in (4 / 9 + (-(kp * Ea) - ι)) 3.7e-8)
    (hφ : |φ| ≤ 1 / 100) (hEa : |Ea| ≤ 13 / 10) (hι : |ι| ≤ 7 / 5000) :
    Near32 (AP_MotorsMulticopter.update_throttle_filter m)._throttle_filter_value
      (4 / 9 + ((1 - am) * φ + am * (-(kp * Ea) - ι))) 2.9e-8 := by
  have hτ : |-(kp * Ea) - ι| ≤ 0.0665 := by
    have := abs_le.1 hEa; have := abs_le.1 hι
    rw [kp_eq]; apply bnd <;> linarith
  obtain ⟨he, hn⟩ := throttle_filter_near m hc hdt (Near32.of_val hF hφv) hT hφ hτ
  rw [he]; exact hn

/-- The actuators of the tick: with the mixer passing the throttle through, in the linear
configuration, every actuator has the value of the throttle filter output. -/
theorem actuators_tick {p : AP_MotorsMulticopter.Params} (hp : LinearConfig p)
    (s : AP_MotorsMatrix.State)
    (hthr : (AP_MotorsMatrix.output_armed_stabilizing p s).thr_lin =
      { lift_max := 1.0, batt_voltage_filt := 1.0 })
    (hen' : (AP_MotorsMatrix.output_armed_stabilizing p s).motor_enabled = #v[true, true, true, true])
    (hmix : MixerPass p s) (h0 : 0 ≤ s._throttle_filter_value.toReal)
    (h1 : s._throttle_filter_value.toReal ≤ 1) :
    ∀ i : Fin 4,
      ((AP_MotorsMatrix.output_to_motors p (AP_MotorsMatrix.output_armed_stabilizing p s)).2[i]).IsFinite ∧
      ((AP_MotorsMatrix.output_to_motors p (AP_MotorsMatrix.output_armed_stabilizing p s)).2[i]).toReal =
        s._throttle_filter_value.toReal :=
  output_to_motors_val hp _ hen' hthr h0 h1 hmix

set_option maxHeartbeats 4000000 in
/-- **One tick of the controller's vertical path.** At a hover sample (hypotheses of the header),
from floats whose exact values `x = vx ζ w Ev Ea I F` lie in the sublevel set `V x ≤ 1/10` and
satisfy the tick invariant, with the sensor readings of `CopterSense` (as `sense_near` gives them),
the new floats computed by `update_throttle_filter`, `AC_P_1D.update_all`,
`AC_PID_Basic.update_all`, `get_accel_ef().z + GRAVITY_MSS`, `AC_PID.update_all`, the hover offset
and `set_throttle_out`, wired as `D_update_controller` wires them, together with the plant's
`ζ + h w`, `w - k h φ'`, have exact values `stepN x n` for perturbations `n` within `NBound`
(`|n1| ≤ 3.6 · 10⁻⁹`, `|n2| ≤ 3.3 · 10⁻⁷`, `|n3| ≤ 1.4 · 10⁻¹⁰`, `|n4| ≤ 2.9 · 10⁻⁸`), and the tick
invariant holds again for the new floats. -/
theorem vert_tick (hN : NarrowSpec 1)
    -- states at the start of the tick
    (sP : AC_P_1D.State) (sv : AC_PID_Basic.State) (sa : AC_PID.State)
    (m : AP_MotorsMulticopter.State)
    (patt : AC_AttitudeControl_Multi.Params) (satt : AC_AttitudeControl_Multi.State)
    (mi : AP_Motors.Inputs)
    -- the plant and the readings
    {ζ w : ℝ} {tgt zs : Float} {ws fs scZ vff aff cp cr : Float32} (ln lp : Bool)
    (hV : V (vx ζ w sv._error sa._error sa._integrator m._throttle_filter_value) ≤ 1 / 10)
    (hI : VInv sv sa m) (hdt : m._dt_s = dtF)
    (hzs : Near64 zs (ζ - 1) 1e-15) (hws : Near32 ws w 6e-10)
    (hfs : Near32 fs (-(k * m._throttle_filter_value.toReal)) 6e-7)
    -- the hover sample (zero half, navigator, C library)
    (htgt : Near64 tgt (-1) 0)
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
    (∃ n : VN, NBound n ∧
      vx (ζ + CopterVert.h * w) (w - k * CopterVert.h * (F'.toReal - 4 / 9)) rv.1._error ra.1._error
        ra.1._integrator F' =
      stepN (vx ζ w sv._error sa._error sa._integrator m._throttle_filter_value) n) ∧
    VInv rv.1 ra.1 { (AP_MotorsMulticopter.update_throttle_filter m) with
      _throttle_in := mo._throttle_in, _throttle_filter_cutoff := mo._throttle_filter_cutoff } := by
  intro F' vt rv atg ra thr mo
  have hu := u32_le; have hu0 := u32_nonneg
  set x := vx ζ w sv._error sa._error sa._integrator m._throttle_filter_value with hx
  -- the box
  have b0 := bound_0 hV; have b1 := bound_1 hV; have b2 := bound_2 hV
  have b3 := bound_3 hV; have b4 := bound_4 hV; have b5 := bound_5 hV
  have hxζ : x.ζ = ζ := rfl
  have hxw : x.w = w := rfl
  have hxEv : x.Ev = sv._error.toReal := rfl
  have hxEa : x.Ea = sa._error.toReal := rfl
  have hxι : x.ι = sa._integrator.toReal - Istar := rfl
  have hxφ : x.φ = m._throttle_filter_value.toReal - 4 / 9 := rfl
  rw [hxζ] at b0; rw [hxw] at b1; rw [hxEv] at b2; rw [hxEa] at b3; rw [hxι] at b4; rw [hxφ] at b5
  have hIs : Istar = 7455795 / 16777216 - 4 / 9 := by rw [Istar, Hf_eq]
  have hIb : |sa._integrator.toReal| ≤ 0.00145 := by
    have := abs_le.1 b4; rw [hIs] at this; apply bnd <;> linarith
  -- motors
  have hF' : Near32 F' (4 / 9 + ((1 - am) * x.φ + am * (-(kp * x.Ea) - x.ι))) 2.9e-8 :=
    motors_tick hI.cutoff hdt hI.F_fin (by rw [hxφ]; ring) hI.throttle b5 b3 b4
  -- position and velocity
  have hp1 := p1d_near hN sP htgt hzs (le_refl _) b0 hmin hmin' hmax hmax' hD1 hD1'
  have hvt : Near32 vt (-(kpos * ζ)) 3.1e-10 := (hp1.1.mul_one hsc).add_zero hvff
  obtain ⟨v1, v2, v3, v4, v5, v6⟩ := pidv_near sv hI.v_reset hI.v_err b2 hI.v_der hI.v_der_b
    hvt hws b0 b1 ln lp
  have hEv'b : |rv.1._error.toReal| ≤ 0.0476 := by
    have := v1.bound
    have : |(1 - av) * sv._error.toReal + av * (-(kpos * ζ) - w)| ≤ 0.04755 := by
      have := abs_le.1 b0; have := abs_le.1 b1; have := abs_le.1 b2
      rw [av_eq, kpos_eq]; apply bnd <;> nlinarith
    linarith
  have hat : Near32 atg (kv * rv.1._error.toReal) 1.5e-8 := (v6.mul_one hsc).add_zero haff
  have hA : |kv * rv.1._error.toReal| ≤ 0.2381 := by
    rw [abs_mul, kv_eq]; norm_num; linarith
  -- acceleration
  have hfs' : Near32 fs (-(k * (x.φ + 4 / 9))) 6e-7 := by
    rw [hxφ, sub_add_cancel]; exact hfs
  have hmeas := accel_meas_near hfs' b5
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9⟩ := pida_near sa hI.a_reset hI.a_tgt hI.a_tgt_b
    hI.a_err b3 hI.a_int hIb hI.a_der hI.a_der_b hat hA hmeas b5
  obtain ⟨q1, q2, q3, q4, q5, q6, q7, q8, -⟩ := pida_eval sa hat.1 hmeas.1 hI.a_reset
  -- throttle
  have hff : Z (AC_PID.get_ff ra.1) := by
    show Z (ra.1._pid_info.FF + ra.1._pid_info.DFF)
    rw [q7, q8]; exact add_Z a8 a9
  have hEa'b : |(aE sa atg (fs + GRAVITY_MSS)).toReal| ≤ 1.099 := by
    have := a1.bound
    have : |(1 - aa) * sa._error.toReal + aa * (kv * rv.1._error.toReal + k * x.φ)| ≤ 1.0989 := by
      have := abs_le.1 b3; have := abs_le.1 b5; have := abs_le.1 hA
      rw [aa_eq, k_eq]; apply bnd <;> nlinarith
    linarith
  have hI'b : |(aI sa atg (fs + GRAVITY_MSS)).toReal| ≤ 0.001726 := by
    have := a2.bound
    have : |sa._integrator.toReal + ki * dtc * (aE sa atg (fs + GRAVITY_MSS)).toReal| ≤ 0.001725 := by
      have h1 := abs_le.1 hIb; have h2 := abs_le.1 hEa'b
      rw [ki_eq, dtc_eq]; apply bnd <;> nlinarith
    linarith
  have hr : |kp * (aE sa atg (fs + GRAVITY_MSS)).toReal + (aI sa atg (fs + GRAVITY_MSS)).toReal| ≤
      0.0568 := by
    have h1 := abs_le.1 hEa'b; have h2 := abs_le.1 hI'b
    rw [kp_eq]; apply bnd <;> nlinarith
  have hthr_eq : thr = -(ra.2 + AC_PID.get_ff ra.1 - hoverF) := by
    show -(ra.2 + AC_PID.get_ff ra.1 - AP_Motors.get_throttle_hover mi) = _
    rw [throttle_hover_eq mi hhov]
  have hthr : Near32 thr (Hf - (kp * (aE sa atg (fs + GRAVITY_MSS)).toReal +
      (aI sa atg (fs + GRAVITY_MSS)).toReal)) 3.7e-8 := by
    rw [hthr_eq]; exact throttle_near a3 hr hff
  obtain ⟨s1, s2, s3⟩ := set_throttle_out_val patt satt mi
    (c := AC_PosControl.POSCONTROL_THROTTLE_CUTOFF_FREQ_HZ) hcp hcr hcos hthr.1
  have hmo : Near32 mo._throttle_in (4 / 9 + (-(kp * ra.1._error.toReal) -
      (ra.1._integrator.toReal - Istar))) 3.7e-8 := by
    refine Near32.of_eq_val s1 s2 (hthr.congr ?_)
    rw [q2, q5, Istar]; ring
  -- the perturbations
  refine ⟨⟨⟨rv.1._error.toReal - ((1 - av) * x.Ev + av * (-(kpos * x.ζ) - x.w)),
    ra.1._error.toReal - ((1 - aa) * x.Ea + aa * (kv * rv.1._error.toReal + k * x.φ)),
    (ra.1._integrator.toReal - Istar) - (x.ι + ki * dtc * ra.1._error.toReal),
    (F'.toReal - 4 / 9) - ((1 - am) * x.φ + am * (-(kp * x.Ea) - x.ι))⟩, ⟨?_, ?_, ?_, ?_⟩, ?_⟩, ?_⟩
  · have := v1.2; rw [hxEv, hxζ, hxw]; exact this.trans (by norm_num)
  · have := a1.2; rw [← q2] at this; rw [hxEa]; exact this.trans (by norm_num)
  · have := a2.2; rw [← q2, ← q5] at this
    show |ra.1._integrator.toReal - Istar - (sa._integrator.toReal - Istar +
      ki * dtc * ra.1._error.toReal)| ≤ _
    have e : ra.1._integrator.toReal - Istar - (sa._integrator.toReal - Istar +
        ki * dtc * ra.1._error.toReal) =
        ra.1._integrator.toReal - (sa._integrator.toReal + ki * dtc * ra.1._error.toReal) := by ring
    rw [e]; exact this.trans (by norm_num)
  · have := hF'.2
    have e : F'.toReal - 4 / 9 - ((1 - am) * x.φ + am * (-(kp * x.Ea) - x.ι)) =
        F'.toReal - (4 / 9 + ((1 - am) * x.φ + am * (-(kp * x.Ea) - x.ι))) := by ring
    rw [e]; exact this.trans (by norm_num)
  · simp only [vx, stepN, hxζ, hxw]
    congr 1 <;> ring
  · -- the invariant again
    refine ⟨v3, v1.1, v4, v5, q6, ?_, ?_, ?_, ?_, ?_, ?_, ?_, s3, ?_⟩
    · rw [q1]; exact a4
    · rw [q1]; exact a5
    · rw [q2]; exact a1.1
    · rw [q5]; exact a2.1
    · rw [q3]; exact a6
    · rw [q3]; exact a7
    · exact hF'.1
    · exact hmo

/-- **Invariance across the tick.** With `vert_tick`, `lyap_stepN` keeps the new exact values in
the sublevel set, hence in the box `|ζ| ≤ 5 mm`, `|w| ≤ 1 cm/s`. -/
theorem vert_tick_V {x x' : VX} (hV : V x ≤ 1 / 10) (h : ∃ n : VN, NBound n ∧ x' = stepN x n) :
    V x' ≤ 1 / 10 ∧ |x'.ζ| ≤ 1 / 200 ∧ |x'.w| ≤ 1 / 100 := by
  obtain ⟨n, hn, rfl⟩ := h
  have := lyap_stepN hV hn
  exact ⟨this, box_of_V this⟩

end

end Contracts.CopterVertNear
