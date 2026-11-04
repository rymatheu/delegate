import Contracts.CopterZeroAtt
import AP_Motors.AP_MotorsMatrix

/-!
# Zero lemma for `AP_MotorsMatrix::output_armed_stabilizing`

With zero roll, pitch and yaw inputs and feed-forwards, all four motors enabled and throttle
factors of value one, the four `_thrust_rpyt_out` are the same value: the throttle
`get_throttle() · compensation_gain` clipped to `[0, throttle_thrust_max]` (`AP_MotorsMatrix.cpp`
`:236-246`), for every throttle. The loops are unrolled; the yaw headroom `yaw_allowed` is not
computed in closed form (it depends on which yaw factors are `is_zero`), only shown never to clip the
zero yaw demand (`yaw_check_false`: `|±0| > MAX(a, b)` is false for every `a` when `b ≥ 0`,
including `a` NaN or infinite).
-/

open Float.Model UnpackedFloat AP_Math AP_MotorsMatrix

namespace Contracts.CopterZero

theorem not_lt_zero_of_gt {a b : Float32} (hb : b.IsFinite) (hb0 : 0 ≤ b.toReal) (h : b < a) :
    ¬ a < 0 := by
  by_cases ha : a.IsFinite
  · rw [lt_iff hb ha] at h; rw [lt_iff ha Float32.isFinite_zero, Float32.toReal_zero]; linarith
  · intro h2
    rw [Float32.lt_iff_unpack] at h h2
    rw [Float32.isFinite_iff] at ha hb
    rw [Float32.toModel_unpack_zero] at h2
    revert h h2 ha hb
    cases a.toModel.unpack with
    | infinity sa =>
      cases sa <;> cases b.toModel.unpack <;>
        simp [UnpackedFloat.lt, UnpackedFloat.compare, UnpackedFloat.isFinite]
    | notANumber => cases b.toModel.unpack <;> simp [UnpackedFloat.lt, UnpackedFloat.compare]
    | _ => simp [UnpackedFloat.isFinite]

/-- The yaw limit never clips a zero yaw demand: `|z| > MAX(a, b)` is false for a zero `z`, a
finite `b ≥ 0` and every `a`. -/
theorem yaw_check_false {z b : Float32} (hz : Z z) (hb : b.IsFinite) (hb0 : 0 ≤ b.toReal)
    (a : Float32) : ¬ (Float32.abs z > MAX a b) := by
  show ¬ (MAX a b < z.abs)
  rw [lt_Z_iff (Z_abs hz), MAX_eq]
  split
  · exact not_lt_zero_of_gt hb hb0 ‹_›
  · rw [lt_iff hb Float32.isFinite_zero, Float32.toReal_zero]; linarith

theorem ite_yield_id {α : Type} {c : Prop} [h : Decidable c] (x y : α) :
    @ite (Id (ForInStep α)) c h (ForInStep.yield x) (ForInStep.yield y) =
      ForInStep.yield (if c then x else y) := by
  split <;> rfl
theorem ite_fst' {α β : Type} {c : Prop} [Decidable c] (x y : α × β) :
    (if c then x else y).1 = if c then x.1 else y.1 := by split <;> rfl
theorem ite_snd' {α β : Type} {c : Prop} [Decidable c] (x y : α × β) :
    (if c then x else y).2 = if c then x.2 else y.2 := by split <;> rfl

/-- `boost_ratio s b x` with `_thrust_boost_ratio` a zero is `x` in value. -/
theorem boost_ratio_Z {s : State} (h : Z s._thrust_boost_ratio) {b x : Float32} (hb : b.IsFinite)
    (hx : x.IsFinite) : (boost_ratio s b x).IsFinite ∧ (boost_ratio s b x).toReal = x.toReal := by
  unfold boost_ratio
  have h1 := Z_mul_left h hb
  have h2 := mul_One_left (One_sub_Z lit_one h) hx
  exact add_Z_left h1 h2.1 |>.imp id (fun e => e.trans h2.2)

theorem mix_c1 (x : Float32) (hx : Z x) : ¬ (x - x > 1.0) := by
  have h := Z_sub hx hx
  show ¬ ((1.0 : Float32) < x - x)
  rw [lt_iff lit_one.1 h.1, h.2, lit_one.2]; norm_num

theorem mix_c2 (a x : Float32) (hx : Z x) (ha : a.IsFinite) (ha0 : 0 ≤ a.toReal) : ¬ (a + x < 0) := by
  have h := add_Z_right ha hx
  rw [lt_iff h.1 Float32.isFinite_zero, h.2, Float32.toReal_zero]; linarith

theorem mix_c3 : ¬ ((1.0 : Float32) < 1.0) := by
  rw [lt_iff lit_one.1 lit_one.1]; exact lt_irrefl _

theorem mix_adj (t x : Float32) (hx : Z x) (ht : t.IsFinite) :
    (t - -(x * 1.0)).IsFinite ∧ (t - -(x * 1.0)).toReal = t.toReal :=
  sub_Z_right ht (Z_neg (Z_mul_left hx lit_one.1))

theorem mix_c4 (t x : Float32) (hx : Z x) (ht : t.IsFinite) (ht0 : 0 ≤ t.toReal) :
    ¬ (t - -(x * 1.0) < 0.0) := by
  have h := mix_adj t x hx ht
  rw [lt_iff h.1 Z_lit0.1, h.2, Z_lit0.2]; linarith

theorem mix_c5 (t x : Float32) (hx : Z x) (ht : t.IsFinite) (ht1 : t.toReal ≤ 1) :
    ¬ (t - -(x * 1.0) > 1.0 - (-(x * 1.0) + x * 1.0)) := by
  have h := mix_adj t x hx ht
  have hm := Z_mul_left hx lit_one.1
  have h2 := One_sub_Z lit_one (Z_add (Z_neg hm) hm)
  show ¬ (_ < _)
  rw [lt_iff h2.1 h.1, h.2, h2.2]; linarith

theorem mix_out {t x y f : Float32} (hx : Z x) (hy : Z y) (ht : t.IsFinite) (hf : One f) :
    ((-(x * 1.0) + (t - -(x * 1.0))) * f + 1.0 * y).IsFinite ∧
      ((-(x * 1.0) + (t - -(x * 1.0))) * f + 1.0 * y).toReal = t.toReal := by
  have h1 := add_Z_left (Z_neg (Z_mul_left hx lit_one.1)) (mix_adj t x hx ht).1
  have h2 := mul_One_right h1.1 hf
  have h3 := add_Z_right h2.1 (Z_mul_right lit_one.1 hy)
  exact ⟨h3.1, h3.2.trans (h2.2.trans (h1.2.trans (mix_adj t x hx ht).2))⟩

/-- The value of every `_thrust_rpyt_out` at zero roll, pitch and yaw: the throttle
`get_throttle() · gain` clipped to `[0, throttle_thrust_max · gain]`. -/
noncomputable def hoverThrust (s : State) (cg : Float32) : ℝ :=
  min (max (AP_Motors.get_throttle s.toInputs * cg).toReal 0) (s._throttle_thrust_max * cg).toReal

set_option maxHeartbeats 4000000 in
/-- **`output_armed_stabilizing` with zero roll, pitch and yaw.** For every throttle, the four
`_thrust_rpyt_out` are finite and equal to `hoverThrust s cg`: the compensated throttle clipped to
`[0, throttle_thrust_max · gain]`. Hypotheses: the compensation gain `cg` finite and at most `10³⁰`,
`_thrust_boost_ratio` a zero (thrust boost off), `throttle_thrust_max · gain` in `[0, 1]`, the yaw
headroom `MOT_YAW_HEADROOM · 0.001` finite and non-negative, the four motors enabled with finite
roll, pitch, yaw factors and throttle factors of value one (quad X after `normalise_rpy_factors`). -/
theorem output_armed_stabilizing_Z (p : AP_MotorsMulticopter.Params) (s : State) {cg : Float32}
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
    (hft : ∀ (i : ℕ) (hi : i < 4), One s._throttle_factor[i]) :
    ((output_armed_stabilizing p s)._thrust_rpyt_out[0].IsFinite ∧
        (output_armed_stabilizing p s)._thrust_rpyt_out[0].toReal = hoverThrust s cg) ∧
      ((output_armed_stabilizing p s)._thrust_rpyt_out[1].IsFinite ∧
        (output_armed_stabilizing p s)._thrust_rpyt_out[1].toReal = hoverThrust s cg) ∧
      ((output_armed_stabilizing p s)._thrust_rpyt_out[2].IsFinite ∧
        (output_armed_stabilizing p s)._thrust_rpyt_out[2].toReal = hoverThrust s cg) ∧
      ((output_armed_stabilizing p s)._thrust_rpyt_out[3].IsFinite ∧
        (output_armed_stabilizing p s)._thrust_rpyt_out[3].toReal = hoverThrust s cg) := by
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
  -- the throttle, the maximum, the average maximum
  have hgt : (AP_Motors.get_throttle s.toInputs).IsFinite ∧
      0 ≤ (AP_Motors.get_throttle s.toInputs).toReal ∧ (AP_Motors.get_throttle s.toInputs).toReal ≤ 1 := by
    unfold AP_Motors.get_throttle
    rw [constrain_float_eq]
    have := Contracts.Float32Clip.constrain_float_spec Z_lit0.1 lit_one.1
      (by rw [Z_lit0.2, lit_one.2]; norm_num)
      (by rw [Z_lit0.2, lit_one.2]; have := maxFinite32_ge; rw [abs_le]; constructor <;> linarith)
      s._throttle_filter_value
    rwa [Z_lit0.2, lit_one.2] at this
  have hgb : |(AP_Motors.get_throttle s.toInputs).toReal| ≤ 1 :=
    abs_le.2 ⟨by linarith [hgt.2.1], hgt.2.2⟩
  have hTf : (AP_Motors.get_throttle s.toInputs * cg).IsFinite := by
    refine fin_mul hgt.1 hcgf ?_
    rw [abs_mul]
    have := abs_nonneg cg.toReal
    have := abs_nonneg (AP_Motors.get_throttle s.toInputs).toReal
    nlinarith
  obtain ⟨hTMf, hTMv⟩ := boost_ratio_Z (s := s) hboost (b := 1.0) lit_one.1 htm.1
  have hA : ∀ t : Float32, t.IsFinite → 0 ≤ t.toReal →
      t.toReal ≤ (boost_ratio s 1.0 (s._throttle_thrust_max * cg)).toReal →
      (constrain_float (s._throttle_avg_max * cg) t (boost_ratio s 1.0 (s._throttle_thrust_max * cg))).IsFinite ∧
      0 ≤ (constrain_float (s._throttle_avg_max * cg) t
        (boost_ratio s 1.0 (s._throttle_thrust_max * cg))).toReal := by
    intro t htf ht0 htle
    rw [constrain_float_eq]
    have hsum : |t.toReal + (boost_ratio s 1.0 (s._throttle_thrust_max * cg)).toReal| ≤ maxFinite32 := by
      have := maxFinite32_ge
      rw [hTMv] at htle ⊢
      rw [abs_le]; constructor <;> linarith [htm.2.2]
    obtain ⟨h1, h2, -⟩ := Contracts.Float32Clip.constrain_float_spec htf hTMf htle hsum
      (s._throttle_avg_max * cg)
    exact ⟨h1, by linarith⟩
  have hE0 := hE 0 (by decide)
  have hE1 := hE 1 (by decide)
  have hE2 := hE 2 (by decide)
  have hE3 := hE 3 (by decide)
  have hf0 := hft 0 (by decide)
  have hf1 := hft 1 (by decide)
  have hf2 := hft 2 (by decide)
  have hf3 := hft 3 (by decide)
  unfold output_armed_stabilizing hoverThrust
  by_cases c1 : AP_Motors.get_throttle s.toInputs * cg ≤ 0.0
  · have hT0 : (AP_Motors.get_throttle s.toInputs * cg).toReal ≤ 0 := by
      rw [le_iff hTf Z_lit0.1, Z_lit0.2] at c1; exact c1
    by_cases c2 : (0.0 : Float32) ≥ boost_ratio s 1.0 (s._throttle_thrust_max * cg)
    · have hTM0 : (boost_ratio s 1.0 (s._throttle_thrust_max * cg)).toReal ≤ 0 := by
        have := (le_iff hTMf Z_lit0.1).1 c2; rwa [Z_lit0.2] at this
      obtain ⟨hAf, hA0⟩ := hA _ hTMf (by rw [hTMv]; exact htm.2.1) le_rfl
      simp only [hcg, Id.run, hfin, h3, hlt, hl1, hg1, List.forIn_cons,
        List.forIn_nil, bind, pure, hen, hpos, if_true, Bool.false_eq_true, if_false, ite_yield_id,
        ite_fst', ite_snd', ite_self, hyc, Fin.getElem_fin, Vector.getElem_set, Fin.isValue, Fin.val_zero,
        Fin.val_one, Fin.val_two, c1, c2, n01, n02, n03, n10, n12, n13, n20, n21, n23, n30, n31, n32,
        mix_c1 _ hE0, mix_c2 _ _ hE0 hAf hA0, mix_c3, mix_c4 _ _ hE0 hTMf (by rw [hTMv]; exact htm.2.1),
        mix_c5 _ _ hE0 hTMf (by rw [hTMv]; exact htm.2.2)]
      have hv : (boost_ratio s 1.0 (s._throttle_thrust_max * cg)).toReal =
          min (max (AP_Motors.get_throttle s.toInputs * cg).toReal 0) (s._throttle_thrust_max * cg).toReal := by
        rw [hTMv, max_eq_right hT0]; rw [hTMv] at hTM0
        rw [min_eq_left htm.2.1]; linarith [htm.2.1]
      exact ⟨(mix_out hE0 hE0 hTMf hf0).imp id (·.trans hv), (mix_out hE0 hE1 hTMf hf1).imp id (·.trans hv),
        (mix_out hE0 hE2 hTMf hf2).imp id (·.trans hv), (mix_out hE0 hE3 hTMf hf3).imp id (·.trans hv)⟩
    · have hTM0 : 0 < (boost_ratio s 1.0 (s._throttle_thrust_max * cg)).toReal := by
        have := c2; rw [ge_iff_le, le_iff hTMf Z_lit0.1, Z_lit0.2] at this; linarith
      obtain ⟨hAf, hA0⟩ := hA _ Z_lit0.1 (by rw [Z_lit0.2]) (by rw [Z_lit0.2]; linarith)
      simp only [hcg, Id.run, hfin, h3, hlt, hl1, hg1, List.forIn_cons,
        List.forIn_nil, bind, pure, hen, hpos, if_true, Bool.false_eq_true, if_false, ite_yield_id,
        ite_fst', ite_snd', ite_self, hyc, Fin.getElem_fin, Vector.getElem_set, Fin.isValue, Fin.val_zero,
        Fin.val_one, Fin.val_two, c1, c2, n01, n02, n03, n10, n12, n13, n20, n21, n23, n30, n31, n32,
        mix_c1 _ hE0, mix_c2 _ _ hE0 hAf hA0, mix_c3, mix_c4 _ _ hE0 Z_lit0.1 (by rw [Z_lit0.2]),
        mix_c5 _ _ hE0 Z_lit0.1 (by rw [Z_lit0.2]; norm_num)]
      have hv : (0.0 : Float32).toReal =
          min (max (AP_Motors.get_throttle s.toInputs * cg).toReal 0) (s._throttle_thrust_max * cg).toReal := by
        rw [Z_lit0.2, max_eq_right hT0, min_eq_left htm.2.1]
      exact ⟨(mix_out hE0 hE0 Z_lit0.1 hf0).imp id (·.trans hv), (mix_out hE0 hE1 Z_lit0.1 hf1).imp id (·.trans hv),
        (mix_out hE0 hE2 Z_lit0.1 hf2).imp id (·.trans hv), (mix_out hE0 hE3 Z_lit0.1 hf3).imp id (·.trans hv)⟩
  · have hT0 : 0 < (AP_Motors.get_throttle s.toInputs * cg).toReal := by
      rw [le_iff hTf Z_lit0.1, Z_lit0.2] at c1; linarith
    by_cases c2 : AP_Motors.get_throttle s.toInputs * cg ≥
        boost_ratio s 1.0 (s._throttle_thrust_max * cg)
    · have hTM1 : (boost_ratio s 1.0 (s._throttle_thrust_max * cg)).toReal ≤
          (AP_Motors.get_throttle s.toInputs * cg).toReal := (le_iff hTMf hTf).1 c2
      obtain ⟨hAf, hA0⟩ := hA _ hTMf (by rw [hTMv]; exact htm.2.1) le_rfl
      simp only [hcg, Id.run, hfin, h3, hlt, hl1, hg1, List.forIn_cons,
        List.forIn_nil, bind, pure, hen, hpos, if_true, Bool.false_eq_true, if_false, ite_yield_id,
        ite_fst', ite_snd', ite_self, hyc, Fin.getElem_fin, Vector.getElem_set, Fin.isValue, Fin.val_zero,
        Fin.val_one, Fin.val_two, c1, c2, n01, n02, n03, n10, n12, n13, n20, n21, n23, n30, n31, n32,
        mix_c1 _ hE0, mix_c2 _ _ hE0 hAf hA0, mix_c3, mix_c4 _ _ hE0 hTMf (by rw [hTMv]; exact htm.2.1),
        mix_c5 _ _ hE0 hTMf (by rw [hTMv]; exact htm.2.2)]
      have hv : (boost_ratio s 1.0 (s._throttle_thrust_max * cg)).toReal =
          min (max (AP_Motors.get_throttle s.toInputs * cg).toReal 0) (s._throttle_thrust_max * cg).toReal := by
        rw [hTMv, max_eq_left hT0.le]; rw [hTMv] at hTM1; rw [min_eq_right hTM1]
      exact ⟨(mix_out hE0 hE0 hTMf hf0).imp id (·.trans hv), (mix_out hE0 hE1 hTMf hf1).imp id (·.trans hv),
        (mix_out hE0 hE2 hTMf hf2).imp id (·.trans hv), (mix_out hE0 hE3 hTMf hf3).imp id (·.trans hv)⟩
    · have hTM1 : (AP_Motors.get_throttle s.toInputs * cg).toReal <
          (boost_ratio s 1.0 (s._throttle_thrust_max * cg)).toReal := by
        have := c2; rw [ge_iff_le, le_iff hTMf hTf] at this; linarith
      obtain ⟨hAf, hA0⟩ := hA _ hTf hT0.le hTM1.le
      simp only [hcg, Id.run, hfin, h3, hlt, hl1, hg1, List.forIn_cons,
        List.forIn_nil, bind, pure, hen, hpos, if_true, Bool.false_eq_true, if_false, ite_yield_id,
        ite_fst', ite_snd', ite_self, hyc, Fin.getElem_fin, Vector.getElem_set, Fin.isValue, Fin.val_zero,
        Fin.val_one, Fin.val_two, c1, c2, n01, n02, n03, n10, n12, n13, n20, n21, n23, n30, n31, n32,
        mix_c1 _ hE0, mix_c2 _ _ hE0 hAf hA0, mix_c3, mix_c4 _ _ hE0 hTf hT0.le,
        mix_c5 _ _ hE0 hTf (by rw [hTMv] at hTM1; linarith [htm.2.2])]
      have hv : (AP_Motors.get_throttle s.toInputs * cg).toReal =
          min (max (AP_Motors.get_throttle s.toInputs * cg).toReal 0) (s._throttle_thrust_max * cg).toReal := by
        rw [max_eq_left hT0.le]; rw [hTMv] at hTM1; rw [min_eq_left hTM1.le]
      exact ⟨(mix_out hE0 hE0 hTf hf0).imp id (·.trans hv), (mix_out hE0 hE1 hTf hf1).imp id (·.trans hv),
        (mix_out hE0 hE2 hTf hf2).imp id (·.trans hv), (mix_out hE0 hE3 hTf hf3).imp id (·.trans hv)⟩

end Contracts.CopterZero
