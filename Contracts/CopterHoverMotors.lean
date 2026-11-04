import Contracts.CopterZeroMotors
import Contracts.CopterVertNearStep
import Contracts.CopterHoverUniverse

/-!
# One call of `Copter.motors_output_main` at the hover

`motors_output_main runParams` writes `air_density_ratio = 1` and runs `AP_MotorsMatrix.output`
with the run's `MOT_` record `CopterVertNear.runMot`: `update_throttle_filter` (only
`_throttle_filter_value` changes, to `F'`), `update_lift_max_from_batt_voltage` (`thr_lin` becomes
`{lift_max := 1, batt_voltage_filt := 1}`), `output_logic` (all `limit` flags cleared,
`_throttle_thrust_max := 1`, `_thrust_boost_ratio := MAX(0, r - dtF / 0.5)`, which is `+0` for a zero
`r`, and the spin-up, throttle-limit and disarm-timer members), `output_armed_stabilizing` (gain
exactly `1`) and `output_to_motors` (linear thrust curve, no slew).

With zero roll, pitch and yaw inputs and `0 < F' < 1` the mixer takes none of its clipping
branches (`oas_frame`): it writes only `_thrust_rpyt_out` and `_throttle_out`, so the `limit` flags
stay as `output_logic` left them, all false. The four thrust values are `F'`
(`CopterZero.output_armed_stabilizing_Z`), hence so are the four actuators
(`CopterVertNear.output_to_motors_val`).

The motor factors enter as finiteness hypotheses (and throttle factors of value one): the factors
of `AP_MotorsMatrix.init` are built from `Float32.cos`, an opaque `extern` constant, so their
finiteness is not a kernel computation.
-/

open Float.Model UnpackedFloat AP_Math AP_MotorsMatrix Contracts.CopterZero

namespace Contracts.CopterHover

/-- `update_throttle_filter` changes only `_throttle_filter_value`. -/
theorem utf_frame (s : AP_MotorsMulticopter.State) :
    AP_MotorsMulticopter.update_throttle_filter s =
      { s with _throttle_filter_value := (AP_MotorsMulticopter.update_throttle_filter s)._throttle_filter_value } := by
  unfold AP_MotorsMulticopter.update_throttle_filter
  simp only [Id.run]
  split_ifs <;> rfl

/-- `output_logic` at the run parameters, field by field (`MOT_SAFE_DISARM = 0`,
`MOT_SPOOL_TIME = 0.5`). -/
theorem ol_frame (s : AP_MotorsMulticopter.State) :
    AP_MotorsMulticopter.output_logic CopterVertNear.runMot s =
      { s with _disarm_safe_timer := CopterVertNear.runMot.MOT_SAFE_TIME,
               limit := s.limit.set_all false, _spin_up_ratio := 1.0, _throttle_limit := 1.0,
               _throttle_thrust_max := 1.0,
               _thrust_boost_ratio := MAX 0.0 (s._thrust_boost_ratio - s._dt_s / 0.5) } := by
  unfold AP_MotorsMulticopter.output_logic AP_MotorsMulticopter.get_current_limit_max_throttle
  have h1 : (CopterVertNear.runMot.MOT_SAFE_DISARM != 0) = false := by decide
  have h2 : (CopterVertNear.runMot.MOT_SPOOL_TIME < 0.05) = False := by
    simp only [eq_iff_iff, iff_false]; decide
  simp only [Id.run, h1, Bool.false_and, Bool.false_eq_true, if_false, h2]
  rfl

set_option maxHeartbeats 400000 in
/-- **The mixer at an unclipped hover throttle changes only its outputs.** Under the hypotheses of
`output_armed_stabilizing_Z` (without the throttle factors), with the compensated throttle strictly
between `0` and `throttle_thrust_max · gain`, `output_armed_stabilizing` takes none of the
branches that set a `limit` flag (`:240`, `:244`, `:331`, `:376-388`): it writes only
`_thrust_rpyt_out` and `_throttle_out`. -/
theorem oas_frame (p : AP_MotorsMulticopter.Params) (s : State) {cg : Float32}
    (hcg : Thrust_Linearization.get_compensation_gain s.thr_lin s.air_density_ratio = cg)
    (hcgf : cg.IsFinite) (hcgb : |cg.toReal| ≤ 1e30)
    (hr : Z s._roll_in) (hrf : Z s._roll_in_ff) (hp : Z s._pitch_in) (hpf : Z s._pitch_in_ff)
    (hy : Z s._yaw_in) (hyf : Z s._yaw_in_ff) (hboost : Z s._thrust_boost_ratio)
    (htm : (s._throttle_thrust_max * cg).IsFinite ∧ 0 ≤ (s._throttle_thrust_max * cg).toReal ∧
      (s._throttle_thrust_max * cg).toReal ≤ 1)
    (hym : (Float32.ofInt p.MOT_YAW_HEADROOM.toInt * 0.001).IsFinite ∧
      0 ≤ (Float32.ofInt p.MOT_YAW_HEADROOM.toInt * 0.001).toReal)
    (hen : ∀ i : Fin 4, s.motor_enabled[i] = true)
    (hfr : ∀ (i : ℕ) (hi : i < 4), (s._roll_factor[i]).IsFinite)
    (hfp : ∀ (i : ℕ) (hi : i < 4), (s._pitch_factor[i]).IsFinite)
    (hfy : ∀ (i : ℕ) (hi : i < 4), (s._yaw_factor[i]).IsFinite)
    (hT0 : 0 < (AP_Motors.get_throttle s.toInputs * cg).toReal)
    (hT1 : (AP_Motors.get_throttle s.toInputs * cg).toReal < (s._throttle_thrust_max * cg).toReal) :
    ∃ t o, output_armed_stabilizing p s = { s with _thrust_rpyt_out := t, _throttle_out := o } := by
  have hfin : List.finRange 4 = [0, 1, 2, 3] := by decide
  have h3 : ((3 : Fin 4) : ℕ) = 3 := rfl
  have hR : Z ((s._roll_in + s._roll_in_ff) * cg) := Z_mul_left (Z_add hr hrf) hcgf
  have hP : Z ((s._pitch_in + s._pitch_in_ff) * cg) := Z_mul_left (Z_add hp hpf) hcgf
  have hY : Z ((s._yaw_in + s._yaw_in_ff) * cg) := Z_mul_left (Z_add hy hyf) hcgf
  have hE : ∀ (i : ℕ) (hi : i < 4), Z ((s._roll_in + s._roll_in_ff) * cg * s._roll_factor[i] +
      (s._pitch_in + s._pitch_in_ff) * cg * s._pitch_factor[i] +
      (s._yaw_in + s._yaw_in_ff) * cg * s._yaw_factor[i]) := fun i hi =>
    Z_add (Z_add (Z_mul_left hR (hfr i hi)) (Z_mul_left hP (hfp i hi))) (Z_mul_left hY (hfy i hi))
  have hpos : ∀ (i : ℕ) (hi : i < 4),
      is_positive ((s._yaw_in + s._yaw_in_ff) * cg * s._yaw_factor[i]) = false :=
    fun i hi => is_positive_Z (Z_mul_left hY (hfy i hi))
  have hlt : ∀ (i j : ℕ) (hi : i < 4) (hj : j < 4), ¬ ((s._roll_in + s._roll_in_ff) * cg * s._roll_factor[i] +
      (s._pitch_in + s._pitch_in_ff) * cg * s._pitch_factor[i] +
      (s._yaw_in + s._yaw_in_ff) * cg * s._yaw_factor[i] < (s._roll_in + s._roll_in_ff) * cg * s._roll_factor[j] +
      (s._pitch_in + s._pitch_in_ff) * cg * s._pitch_factor[j] +
      (s._yaw_in + s._yaw_in_ff) * cg * s._yaw_factor[j]) := fun i j hi hj => by
    rw [lt_iff (hE i hi).1 (hE j hj).1, (hE i hi).2, (hE j hj).2]; exact lt_irrefl 0
  have hl1 : ∀ (i : ℕ) (hi : i < 4), (s._roll_in + s._roll_in_ff) * cg * s._roll_factor[i] +
      (s._pitch_in + s._pitch_in_ff) * cg * s._pitch_factor[i] +
      (s._yaw_in + s._yaw_in_ff) * cg * s._yaw_factor[i] < 1.0 := fun i hi => by
    rw [lt_iff (hE i hi).1 lit_one.1, (hE i hi).2, lit_one.2]; norm_num
  have hg1 : ∀ (i : ℕ) (hi : i < 4), (s._roll_in + s._roll_in_ff) * cg * s._roll_factor[i] +
      (s._pitch_in + s._pitch_in_ff) * cg * s._pitch_factor[i] +
      (s._yaw_in + s._yaw_in_ff) * cg * s._yaw_factor[i] > -1.0 := fun i hi => by
    show (-1.0 : Float32) < _
    rw [lt_iff lit_neg_one.1 (hE i hi).1, (hE i hi).2, lit_neg_one.2]; norm_num
  obtain ⟨hymf, hymv⟩ := boost_ratio_Z (s := s) hboost (b := 0.5) lit_half.1 hym.1
  have hyc0 := yaw_check_false hY hymf (hymv ▸ hym.2)
  have hyc : ∀ (st : State) (a : Float32), st._thrust_boost_ratio = s._thrust_boost_ratio →
      ¬ (Float32.abs ((s._yaw_in + s._yaw_in_ff) * cg) >
        MAX a (boost_ratio st 0.5 (Float32.ofInt p.MOT_YAW_HEADROOM.toInt * 0.001))) := by
    intro st a h
    have := hyc0 a
    unfold boost_ratio at this ⊢
    rwa [h]
  have n : ((0:ℕ) = 1) = False ∧ ((0:ℕ) = 2) = False ∧ ((0:ℕ) = 3) = False ∧ ((1:ℕ) = 0) = False ∧
      ((1:ℕ) = 2) = False ∧ ((1:ℕ) = 3) = False ∧ ((2:ℕ) = 0) = False ∧ ((2:ℕ) = 1) = False ∧
      ((2:ℕ) = 3) = False ∧ ((3:ℕ) = 0) = False ∧ ((3:ℕ) = 1) = False ∧ ((3:ℕ) = 2) = False := by
    decide
  obtain ⟨n01, n02, n03, n10, n12, n13, n20, n21, n23, n30, n31, n32⟩ := n
  have hgt : (AP_Motors.get_throttle s.toInputs).IsFinite ∧
      0 ≤ (AP_Motors.get_throttle s.toInputs).toReal ∧ (AP_Motors.get_throttle s.toInputs).toReal ≤ 1 := by
    unfold AP_Motors.get_throttle
    rw [constrain_float_eq]
    have := Contracts.Float32Clip.constrain_float_spec Z_lit0.1 lit_one.1
      (by rw [Z_lit0.2, lit_one.2]; norm_num)
      (by rw [Z_lit0.2, lit_one.2]; have := maxFinite32_ge; rw [abs_le]; constructor <;> linarith)
      s._throttle_filter_value
    rwa [Z_lit0.2, lit_one.2] at this
  have hTf : (AP_Motors.get_throttle s.toInputs * cg).IsFinite := by
    refine fin_mul hgt.1 hcgf ?_
    rw [abs_mul]
    have := abs_nonneg cg.toReal
    have := abs_nonneg (AP_Motors.get_throttle s.toInputs).toReal
    have : |(AP_Motors.get_throttle s.toInputs).toReal| ≤ 1 :=
      abs_le.2 ⟨by linarith [hgt.2.1], hgt.2.2⟩
    nlinarith
  obtain ⟨hTMf, hTMv⟩ := boost_ratio_Z (s := s) hboost (b := 1.0) lit_one.1 htm.1
  have hTM1 : (AP_Motors.get_throttle s.toInputs * cg).toReal <
      (boost_ratio s 1.0 (s._throttle_thrust_max * cg)).toReal := by rw [hTMv]; exact hT1
  have c1 : ¬ (AP_Motors.get_throttle s.toInputs * cg ≤ 0.0) := by
    rw [le_iff hTf Z_lit0.1, Z_lit0.2]; linarith
  have c2 : ¬ (AP_Motors.get_throttle s.toInputs * cg ≥ boost_ratio s 1.0 (s._throttle_thrust_max * cg)) := by
    rw [ge_iff_le, le_iff hTMf hTf]; linarith
  have hAf : (constrain_float (s._throttle_avg_max * cg) (AP_Motors.get_throttle s.toInputs * cg)
      (boost_ratio s 1.0 (s._throttle_thrust_max * cg))).IsFinite ∧
      0 ≤ (constrain_float (s._throttle_avg_max * cg) (AP_Motors.get_throttle s.toInputs * cg)
        (boost_ratio s 1.0 (s._throttle_thrust_max * cg))).toReal := by
    rw [constrain_float_eq]
    have hsum : |(AP_Motors.get_throttle s.toInputs * cg).toReal +
        (boost_ratio s 1.0 (s._throttle_thrust_max * cg)).toReal| ≤ maxFinite32 := by
      have := maxFinite32_ge
      rw [hTMv] at hTM1 ⊢
      rw [abs_le]; constructor <;> linarith [htm.2.2]
    obtain ⟨h1, h2, -⟩ := Contracts.Float32Clip.constrain_float_spec hTf hTMf hTM1.le hsum
      (s._throttle_avg_max * cg)
    exact ⟨h1, by linarith⟩
  have hE0 := hE 0 (by decide)
  unfold output_armed_stabilizing
  simp only [hcg, Id.run, hfin, h3, hlt, hl1, hg1, List.forIn_cons,
    List.forIn_nil, bind, pure, hen, hpos, if_true, Bool.false_eq_true, if_false, ite_yield_id,
    ite_fst', ite_snd', ite_self, hyc, Fin.getElem_fin, Vector.getElem_set, Fin.isValue, Fin.val_zero,
    Fin.val_one, Fin.val_two, c1, c2, n01, n02, n03, n10, n12, n13, n20, n21, n23, n30, n31, n32,
    mix_c1 _ hE0, mix_c2 _ _ hE0 hAf.1 hAf.2, mix_c3, mix_c4 _ _ hE0 hTf hT0.le,
    mix_c5 _ _ hE0 hTf (by rw [hTMv] at hTM1; linarith [htm.2.2])]
  exact ⟨_, _, rfl⟩

/-- The spool step of `output_logic` at `dtF` takes a zero boost ratio to `+0`: `MAX(0, r - dtF / 0.5)`
with `r` a zero and the step positive. -/
theorem boost_step_Z {r : Float32} (hr : Z r) : Z (MAX 0.0 (r - CopterVertNear.dtF / 0.5)) := by
  have hq : (CopterVertNear.dtF / (0.5 : Float32)).IsFinite := by decide
  have hqp := is_positive_ge hq (by decide)
  have h := sub_Z_left hr hq
  rw [MAX_eq, if_pos]
  · exact Z_lit0
  · show r - CopterVertNear.dtF / 0.5 < 0.0
    rw [lt_iff h.1 Z_lit0.1, h.2, Z_lit0.2]
    have : (0 : ℝ) < 2 ^ (-23 : ℤ) := by positivity
    linarith

/-- The throttle filter update leaves `air_density_ratio` out of its result's filter value. -/
theorem utf_air (t : AP_MotorsMulticopter.State) (a : Float32) :
    (AP_MotorsMulticopter.update_throttle_filter { t with air_density_ratio := a })._throttle_filter_value =
      (AP_MotorsMulticopter.update_throttle_filter t)._throttle_filter_value := by
  unfold AP_MotorsMulticopter.update_throttle_filter
  simp only [Id.run]
  split_ifs <;> rfl

/-- The yaw headroom of the run, `200 · 0.001`, is finite and non-negative. -/
theorem yaw_headroom_run :
    (Float32.ofInt CopterVertNear.runMot.MOT_YAW_HEADROOM.toInt * 0.001).IsFinite ∧
      0 ≤ (Float32.ofInt CopterVertNear.runMot.MOT_YAW_HEADROOM.toInt * 0.001).toReal := by
  have he : Float32.ofInt CopterVertNear.runMot.MOT_YAW_HEADROOM.toInt * 0.001 = (0.2 : Float32) := by
    decide
  rw [he]
  have hf : (0.2 : Float32).IsFinite := by decide
  refine ⟨hf, ?_⟩
  have := is_positive_ge hf (by decide)
  have : (0 : ℝ) < 2 ^ (-23 : ℤ) := by positivity
  linarith

/-- The state `output_armed_stabilizing` sees at the hover: the motors object after the filter
update (output `F`), `update_lift_max_from_batt_voltage` and `output_logic`. -/
def preMix (m : State) (F : Float32) : State :=
  { m with
    _throttle_filter_value := F
    thr_lin := { lift_max := 1.0, batt_voltage_filt := 1.0 }
    _disarm_safe_timer := CopterVertNear.runMot.MOT_SAFE_TIME
    limit := m.limit.set_all false
    _spin_up_ratio := 1.0
    _throttle_limit := 1.0
    _throttle_thrust_max := 1.0
    _thrust_boost_ratio := MAX 0.0 (m._thrust_boost_ratio - m._dt_s / 0.5) }

/-- `output` as the composition of its four steps. -/
theorem output_steps (p : AP_MotorsMulticopter.Params) (m : State) :
    AP_MotorsMatrix.output p m =
      output_to_motors p (output_armed_stabilizing p { m with
        toState := AP_MotorsMulticopter.output_logic p
          { AP_MotorsMulticopter.update_throttle_filter m.toState with
            thr_lin := Thrust_Linearization.update_lift_max_from_batt_voltage p.toParams
              (AP_MotorsMulticopter.update_throttle_filter m.toState).thr_lin } }) := rfl

/-- `output` at the run parameters unfolded up to the mixer. -/
theorem output_eq (m : State) :
    AP_MotorsMatrix.output CopterVertNear.runMot m =
      output_to_motors CopterVertNear.runMot (output_armed_stabilizing CopterVertNear.runMot
        (preMix m (AP_MotorsMulticopter.update_throttle_filter m.toState)._throttle_filter_value)) := by
  rw [output_steps, utf_frame, ol_frame]
  rfl

/-- `output_to_motors` stores the actuators it returns. -/
theorem output_to_motors_fst (p : AP_MotorsMulticopter.Params) (m : State) :
    (output_to_motors p m).1 = { m with _actuator := (output_to_motors p m).2 } := rfl

/-- **`output` at the hover, on the motors object.** With the air density ratio `1`, the four
motors enabled, finite roll, pitch and yaw factors, throttle factors of value one, zero
roll, pitch, yaw inputs and feed-forwards, a zero boost ratio, the period `dtF` and the new
throttle filter output `F'` finite in `(0, 1)`: the new motors object is `preMix m F'` with new
`_thrust_rpyt_out`, `_throttle_out` and `_actuator` (the returned actuators), and each actuator
is finite of value `F'`. -/
theorem output_hover (m : State) (hair : m.air_density_ratio = 1.0)
    (hen : m.motor_enabled = #v[true, true, true, true])
    (hfr : ∀ i : Fin 4, (m._roll_factor[i]).IsFinite)
    (hfp : ∀ i : Fin 4, (m._pitch_factor[i]).IsFinite)
    (hfy : ∀ i : Fin 4, (m._yaw_factor[i]).IsFinite)
    (hft : ∀ i : Fin 4, CopterZero.One m._throttle_factor[i])
    (hr : Z m._roll_in) (hrff : Z m._roll_in_ff) (hp : Z m._pitch_in)
    (hpff : Z m._pitch_in_ff) (hy : Z m._yaw_in) (hyff : Z m._yaw_in_ff)
    (hboost : Z m._thrust_boost_ratio) (hdt : m._dt_s = CopterVertNear.dtF)
    (hF : (AP_MotorsMulticopter.update_throttle_filter m.toState)._throttle_filter_value.IsFinite)
    (hF0 : 0 < (AP_MotorsMulticopter.update_throttle_filter m.toState)._throttle_filter_value.toReal)
    (hF1 : (AP_MotorsMulticopter.update_throttle_filter m.toState)._throttle_filter_value.toReal < 1) :
    let F' := (AP_MotorsMulticopter.update_throttle_filter m.toState)._throttle_filter_value
    let r := AP_MotorsMatrix.output CopterVertNear.runMot m
    (∃ t o, r.1 = { preMix m F' with _thrust_rpyt_out := t, _throttle_out := o, _actuator := r.2 }) ∧
      ∀ i : Fin 4, (r.2[i]).IsFinite ∧ (r.2[i]).toReal = F'.toReal := by
  intro F' r
  set s3 := preMix m F' with hs3
  have hr' : r = output_to_motors CopterVertNear.runMot (output_armed_stabilizing CopterVertNear.runMot s3) :=
    output_eq m
  have hcg : Thrust_Linearization.get_compensation_gain s3.thr_lin s3.air_density_ratio = 1.0 := by
    show Thrust_Linearization.get_compensation_gain { lift_max := 1.0, batt_voltage_filt := 1.0 }
      m.air_density_ratio = 1.0
    rw [hair]; decide
  have hcgb : |(1.0 : Float32).toReal| ≤ 1e30 := by rw [lit_one.2]; norm_num
  have hb3 : Z s3._thrust_boost_ratio := by
    show Z (MAX 0.0 (m._thrust_boost_ratio - m._dt_s / 0.5))
    rw [hdt]; exact boost_step_Z hboost
  have h11 : CopterZero.One ((1.0 : Float32) * 1.0) := One_mul lit_one lit_one
  have htm : (s3._throttle_thrust_max * 1.0).IsFinite ∧ 0 ≤ (s3._throttle_thrust_max * 1.0).toReal ∧
      (s3._throttle_thrust_max * 1.0).toReal ≤ 1 := by
    show ((1.0 : Float32) * 1.0).IsFinite ∧ 0 ≤ ((1.0 : Float32) * 1.0).toReal ∧
      ((1.0 : Float32) * 1.0).toReal ≤ 1
    exact ⟨h11.1, by rw [h11.2]; norm_num, by rw [h11.2]⟩
  have hen3 : ∀ i : Fin 4, s3.motor_enabled[i] = true := by
    intro i; show m.motor_enabled[i] = true; rw [hen]; fin_cases i <;> rfl
  have hfr3 : ∀ (i : ℕ) (hi : i < 4), (s3._roll_factor[i]).IsFinite := fun i hi => hfr ⟨i, hi⟩
  have hfp3 : ∀ (i : ℕ) (hi : i < 4), (s3._pitch_factor[i]).IsFinite := fun i hi => hfp ⟨i, hi⟩
  have hfy3 : ∀ (i : ℕ) (hi : i < 4), (s3._yaw_factor[i]).IsFinite := fun i hi => hfy ⟨i, hi⟩
  have hft3 : ∀ (i : ℕ) (hi : i < 4), CopterZero.One s3._throttle_factor[i] := fun i hi => hft ⟨i, hi⟩
  have hgt : AP_Motors.get_throttle s3.toInputs = F' :=
    CopterVertNear.constrain_float_of_le hF Z_lit0.1 lit_one.1 (by rw [Z_lit0.2]; exact hF0.le)
      (by rw [lit_one.2]; exact hF1.le)
  have hT := mul_One_right hF lit_one
  obtain ⟨t, o, hoas⟩ := oas_frame CopterVertNear.runMot s3 hcg lit_one.1 hcgb hr hrff hp hpff hy hyff
    hb3 htm yaw_headroom_run hen3 hfr3 hfp3 hfy3
    (by rw [hgt, hT.2]; exact hF0) (by rw [hgt, hT.2, show s3._throttle_thrust_max = 1.0 from rfl, h11.2]; exact hF1)
  obtain ⟨z0, z1, z2, z3⟩ := output_armed_stabilizing_Z CopterVertNear.runMot s3 hcg lit_one.1 hcgb
    hr hrff hp hpff hy hyff hb3 htm yaw_headroom_run hen3 hfr3 hfp3 hfy3 hft3
  have hv : hoverThrust s3 1.0 = F'.toReal := by
    unfold hoverThrust
    rw [hgt, hT.2, show s3._throttle_thrust_max = 1.0 from rfl, h11.2, max_eq_left hF0.le,
      min_eq_left hF1.le]
  have hval : ∀ i : Fin 4, ((output_armed_stabilizing CopterVertNear.runMot s3)._thrust_rpyt_out[i]).IsFinite ∧
      ((output_armed_stabilizing CopterVertNear.runMot s3)._thrust_rpyt_out[i]).toReal = F'.toReal := by
    intro i
    fin_cases i
    · exact ⟨z0.1, z0.2.trans hv⟩
    · exact ⟨z1.1, z1.2.trans hv⟩
    · exact ⟨z2.1, z2.2.trans hv⟩
    · exact ⟨z3.1, z3.2.trans hv⟩
  have hen4 : (output_armed_stabilizing CopterVertNear.runMot s3).motor_enabled = #v[true, true, true, true] := by
    rw [hoas]; exact hen
  have hthr4 : (output_armed_stabilizing CopterVertNear.runMot s3).thr_lin =
      { lift_max := 1.0, batt_voltage_filt := 1.0 } := by
    rw [hoas]; rfl
  refine ⟨⟨t, o, ?_⟩, ?_⟩
  · rw [hr', output_to_motors_fst, hoas]
  · rw [hr']
    exact CopterVertNear.output_to_motors_val CopterVertNear.runMot_linear _ hen4 hthr4 hF0.le hF1.le hval

/-- **`motors_output_main` at the hover.** One call with the run parameters, from a state whose
motors object has the four motors enabled, finite roll, pitch and yaw factors, throttle factors of
value one, zero roll, pitch and yaw inputs and feed-forwards, a zero boost ratio and the period
`dtF`, and whose new throttle filter output `F'` is finite in `(0, 1)`: only `motors` and
`actuators` change (the latter to the motors' `_actuator`); the filter output is `F'`; the
throttle input, filter cutoff, hover throttle, average maximum, enabled motors, factors, period
and `rpy` inputs are unchanged; `throttle_lower` and `throttle_upper` are false; the boost ratio
is a zero; and the four actuators are finite of value `F'`. -/
theorem motors_output_main_hover (s : Copter.State)
    (hen : s.motors.motor_enabled = #v[true, true, true, true])
    (hfr : ∀ i : Fin 4, (s.motors._roll_factor[i]).IsFinite)
    (hfp : ∀ i : Fin 4, (s.motors._pitch_factor[i]).IsFinite)
    (hfy : ∀ i : Fin 4, (s.motors._yaw_factor[i]).IsFinite)
    (hft : ∀ i : Fin 4, CopterZero.One s.motors._throttle_factor[i])
    (hr : Z s.motors._roll_in) (hrff : Z s.motors._roll_in_ff) (hp : Z s.motors._pitch_in)
    (hpff : Z s.motors._pitch_in_ff) (hy : Z s.motors._yaw_in) (hyff : Z s.motors._yaw_in_ff)
    (hboost : Z s.motors._thrust_boost_ratio) (hdt : s.motors._dt_s = CopterVertNear.dtF)
    (hF : (AP_MotorsMulticopter.update_throttle_filter s.motors.toState)._throttle_filter_value.IsFinite)
    (hF0 : 0 < (AP_MotorsMulticopter.update_throttle_filter s.motors.toState)._throttle_filter_value.toReal)
    (hF1 : (AP_MotorsMulticopter.update_throttle_filter s.motors.toState)._throttle_filter_value.toReal < 1) :
    let F' := (AP_MotorsMulticopter.update_throttle_filter s.motors.toState)._throttle_filter_value
    let s' := Copter.motors_output_main runParams s
    (∃ m : AP_MotorsMatrix.State, s' = { s with motors := m, actuators := m._actuator }) ∧
    s'.motors._throttle_filter_value = F' ∧
    s'.motors._throttle_in = s.motors._throttle_in ∧
    s'.motors._throttle_filter_cutoff = s.motors._throttle_filter_cutoff ∧
    s'.motors._throttle_hover = s.motors._throttle_hover ∧
    s'.motors._throttle_avg_max = s.motors._throttle_avg_max ∧
    s'.motors.limit.throttle_lower = false ∧ s'.motors.limit.throttle_upper = false ∧
    s'.motors.motor_enabled = s.motors.motor_enabled ∧
    s'.motors._roll_factor = s.motors._roll_factor ∧ s'.motors._pitch_factor = s.motors._pitch_factor ∧
    s'.motors._yaw_factor = s.motors._yaw_factor ∧
    s'.motors._throttle_factor = s.motors._throttle_factor ∧
    Z s'.motors._thrust_boost_ratio ∧ s'.motors._dt_s = s.motors._dt_s ∧
    s'.motors._roll_in = s.motors._roll_in ∧ s'.motors._roll_in_ff = s.motors._roll_in_ff ∧
    s'.motors._pitch_in = s.motors._pitch_in ∧ s'.motors._pitch_in_ff = s.motors._pitch_in_ff ∧
    s'.motors._yaw_in = s.motors._yaw_in ∧ s'.motors._yaw_in_ff = s.motors._yaw_in_ff ∧
    ∀ i : Fin 4, (s'.actuators[i]).IsFinite ∧ (s'.actuators[i]).toReal = F'.toReal := by
  intro F' s'
  set m0 : State := { s.motors with air_density_ratio := runParams.air_density_ratio } with hm0
  have e : (AP_MotorsMulticopter.update_throttle_filter m0.toState)._throttle_filter_value = F' :=
    utf_air s.motors.toState _
  obtain ⟨⟨t, o, h1⟩, hact⟩ := output_hover m0 rfl hen hfr hfp hfy hft hr hrff hp hpff hy hyff
    hboost hdt (e ▸ hF) (e ▸ hF0) (e ▸ hF1)
  have hY : (AP_MotorsMatrix.output CopterVertNear.runMot m0).1._actuator =
      (AP_MotorsMatrix.output CopterVertNear.runMot m0).2 := by rw [h1]
  have h0 : s' = { s with
      motors := (AP_MotorsMatrix.output CopterVertNear.runMot m0).1
      actuators := (AP_MotorsMatrix.output CopterVertNear.runMot m0).1._actuator } := by
    rw [hY]; rfl
  have hm : s'.motors = (AP_MotorsMatrix.output CopterVertNear.runMot m0).1 := rfl
  have ha : s'.actuators = (AP_MotorsMatrix.output CopterVertNear.runMot m0).2 := rfl
  rw [h1] at hm
  rw [e] at hact hm
  rw [ha, hm]
  refine ⟨⟨(AP_MotorsMatrix.output CopterVertNear.runMot m0).1, ?_⟩, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    rfl, rfl, rfl, rfl, rfl, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, hact⟩
  · exact h0
  · show Z (MAX 0.0 (s.motors._thrust_boost_ratio - s.motors._dt_s / 0.5))
    rw [hdt]; exact boost_step_Z hboost

end Contracts.CopterHover
