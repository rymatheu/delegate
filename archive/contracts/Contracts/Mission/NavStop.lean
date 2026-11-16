import Contracts.Mission.NavFloat
import Contracts.Mission.SubSpec

/-!
# Milestone (a): the loiter target bound

When the mission completes, `loiter_start` (`Vehicle.lean`) sets the navigator's destination to the
stopping point `get_wp_stopping_point_NED_m`, which `AC_PosControl` computes from the estimates of
the tick: the sampled position and velocity. This file bounds that point:

* `stop_NE_bound`: horizontally it is within `⅔ |v|` (times `1 + 2⁻¹⁹`) of the sampled position
  (`min(|v|, WP_SPD)/PSC_NE_POS_P` along `v`, with `WP_SPD = 1`, `PSC_NE_POS_P = 1.5` and the
  navigator's `WP_ACC = 1.5`);
* `stop_D_bound`: vertically within `|v_D|` (times `1 + 2⁻¹⁹`) plus the `float` rounding of the
  position, for `|v_D| < 1` (`PSC_D_POS_P = 1`, `WP_ACC_Z = 1`);
* `loiter_dest_bound`: hence within `d + |v| (1 + 2⁻¹⁸) + 10⁻⁶` of any point within `d` of the
  sampled position; with the rest condition of `ψnavA` (`|v| ≤ rRest + δv`) and the sampled position
  within `δs` of `w7`, the loiter destination is within `0.1521 ≤ ρ` of `w7`.
-/

namespace Contracts.Mission

open Float.Model UnpackedFloat AC_PosControl_lib

noncomputable section

/-! ## The comparisons of `AP_Math` -/

theorem f32_toReal_eps : (1.1920929e-7 : Float32).toReal = 2 ^ (-23 : ℤ) := by
  rw [f32_toReal_1p1920929Em7]; norm_num

theorem isPos_iff {x : Float32} (hx : x.IsFinite) :
    is_positive_float x = true ↔ 2 ^ (-23 : ℤ) ≤ x.toReal := by
  show decide ((1.1920929e-7 : Float32) ≤ x) = true ↔ _
  rw [decide_eq_true_iff, Float32.le_iff_toReal_le f32_isFinite_1p1920929Em7 hx, f32_toReal_eps]

theorem isPosAP_iff {x : Float32} (hx : x.IsFinite) :
    is_positive_AP_Float x = true ↔ 2 ^ (-23 : ℤ) ≤ x.toReal := by
  show decide ((1.1920929e-7 : Float32) ≤ x) = true ↔ _
  rw [decide_eq_true_iff, Float32.le_iff_toReal_le f32_isFinite_1p1920929Em7 hx, f32_toReal_eps]

theorem isZero_iff {x : Float32} (hx : x.IsFinite) :
    is_zero_float x = true ↔ |x.toReal| < 2 ^ (-23 : ℤ) := by
  show decide (Float32.abs x < (1.1920929e-7 : Float32)) = true ↔ _
  rw [decide_eq_true_iff, Float32.lt_iff_toReal_lt ((Float32.isFinite_abs x).2 hx) f32_isFinite_1p1920929Em7,
    Float32.toReal_abs, f32_toReal_eps]

theorem Float32.isNaN_of_isFinite {x : Float32} (hx : x.IsFinite) : Float32.isNaN x = false := by
  have h : x.toModel.unpack.isFinite = true := hx
  show x.toModel.unpack.isNaN = false
  cases hu : x.toModel.unpack <;> simp_all [UnpackedFloat.isFinite, UnpackedFloat.isNaN]

/-- `is_negative` of a nonnegative float is false. -/
theorem isNeg_false (hL : LibmSpec) {x : Float32} (hx : x.IsFinite) (h0 : 0 ≤ x.toReal) :
    is_negative_float x = false := by
  show decide (Float32.toFloat x ≤ -(1.0 : Float) * Float32.toFloat (1.1920929e-7 : Float32)) = false
  rw [decide_eq_false_iff_not]
  obtain ⟨f1, e1⟩ := hL.f32ToF64 x hx
  obtain ⟨f2, e2⟩ := hL.f32ToF64 _ f32_isFinite_1p1920929Em7
  have fm1 : (-(1.0 : Float)).IsFinite := (Float.isFinite_neg _).2 f64_isFinite_1p0
  have em1 : (-(1.0 : Float)).toReal = -1 := by rw [Float.toReal_neg, f64_toReal_1p0]
  have hm := A64.mul (A64.of_exact fm1) (A64.of_exact f2)
    (by rw [e2, f32_toReal_eps, em1]; norm_num)
  rw [Float.le_iff_toReal_le f1 hm.1, e1]
  intro h
  have := (abs_le.1 hm.2).2
  rw [e2, f32_toReal_eps, em1] at this
  have hη := η64_small
  simp only [u64] at this
  norm_num at this
  linarith

/-- `constrain_value` of finite floats with `low ≤ high` is the real clamp. -/
theorem constrain_spec {amt low high : Float32} (line : UInt32) (ha : amt.IsFinite)
    (hl : low.IsFinite) (hh : high.IsFinite) (hlh : low.toReal ≤ high.toReal) :
    (constrain_value_line_float amt low high line).IsFinite ∧
      (constrain_value_line_float amt low high line).toReal =
        max low.toReal (min high.toReal amt.toReal) := by
  simp only [constrain_value_line_float, Id.run, Float32.isNaN_of_isFinite ha,
    Bool.false_eq_true, ite_false, id_pure_eq]
  by_cases h1 : amt < low
  · rw [ite_eq_left h1]
    have := (Float32.lt_iff_toReal_lt ha hl).1 h1
    exact ⟨hl, by rw [min_eq_right (by linarith), max_eq_left this.le]⟩
  · rw [ite_eq_right h1]
    have h1' : low.toReal ≤ amt.toReal := not_lt.1 ((Float32.lt_iff_toReal_lt ha hl).not.1 h1)
    by_cases h2 : amt > high
    · rw [ite_eq_left h2]
      have := (Float32.lt_iff_toReal_lt hh ha).1 h2
      exact ⟨hh, by rw [min_eq_left this.le, max_eq_right hlh]⟩
    · rw [ite_eq_right h2]
      have h2' : amt.toReal ≤ high.toReal :=
        not_lt.1 ((Float32.lt_iff_toReal_lt hh ha).not.1 h2)
      exact ⟨ha, by rw [min_eq_right h2', max_eq_right h1']⟩

/-! ## `inv_sqrt_controller` with `p = D_max = 1.5` -/

theorem f32_div_1p5 : (1.5 : Float32) / 1.5 = 1 := by decide

/-- `inv_sqrt_controller o 1.5 1.5` for `0 ≤ o ≤ 1` is `o / 1.5`, up to rounding. -/
theorem invSqrt_15 (hL : LibmSpec) {o : Float32} (ho : o.IsFinite) (h0 : 0 ≤ o.toReal)
    (h1 : o.toReal ≤ 1) :
    (inv_sqrt_controller o 1.5 1.5).IsFinite ∧
      |(inv_sqrt_controller o 1.5 1.5).toReal - o.toReal / 1.5| ≤ 2 ^ (-20 : ℤ) * o.toReal + η32 := by
  have hn : is_negative_float 1.5 = false :=
    isNeg_false hL f32_isFinite_1p5 (by rw [f32_toReal_1p5]; norm_num)
  have hz : is_zero_float 1.5 = false := by decide
  simp only [inv_sqrt_controller, Id.run, hn, hz, f32_div_1p5, Bool.and_false,
    Bool.false_eq_true, ite_false, Bool.or_false, Bool.not_false, Bool.and_true, id_pure_eq]
  have hab := (Float32.isFinite_abs o).2 ho
  by_cases hlt : Float32.abs o < 1
  · rw [ite_eq_left hlt]
    have hd := A32.div (A32.of_exact ho) (A32.of_exact f32_isFinite_1p5) (m := 1)
      (by norm_num) (by rw [f32_toReal_1p5]; norm_num) (by
        rw [f32_toReal_1p5, abs_of_nonneg (by positivity)]; norm_num
        have : o.toReal / (3 / 2) ≤ 1 := by rw [div_le_one (by norm_num)]; linarith
        nlinarith)
    refine ⟨hd.1, ?_⟩
    have := hd.2
    rw [f32_toReal_1p5] at this
    simp only [abs_of_nonneg (by positivity : 0 ≤ o.toReal / (3 / 2)), mul_zero, add_zero] at this
    norm_num at this ⊢
    have hu : u32 * (o.toReal * (2 / 3)) ≤ 2 ^ (-20 : ℤ) * o.toReal := by
      simp only [u32]; norm_num; nlinarith
    linarith
  · rw [ite_eq_right hlt]
    have hge : 1 ≤ o.toReal := by
      have := (Float32.lt_iff_toReal_lt hab Float32.isFinite_one).not.1 hlt
      rw [Float32.toReal_abs, Float32.toReal_one, not_lt, abs_of_nonneg h0] at this
      exact this
    have ho1 : o.toReal = 1 := le_antisymm h1 hge
    have hp : is_positive_float o = true := (isPos_iff ho).2 (by rw [ho1]; norm_num)
    rw [ite_eq_left hp]
    have h15 := A32.of_exact f32_isFinite_1p5
    rw [f32_toReal_1p5] at h15
    have hoo := A32.of_exact ho
    rw [ho1] at hoo
    obtain ⟨t2f, t2e⟩ := hL.f64ToF32_exact 2.0 2.0 f64_isFinite_2p0 f32_isFinite_2p0
      (by rw [f32_toReal_2p0, f64_toReal_2p0])
    have ht2 : A32 (Float.toFloat32 2.0) 2 0 := ⟨t2f, by rw [t2e, f64_toReal_2p0]; simp⟩
    have hsq := A32.mul h15 h15 (by norm_num [capF])
    have hdv := A32.div h15 hsq (m := 2) (by norm_num) (by
      simp only [u32]; rw [η32_eq]; norm_num) (by
      simp only [u32]; rw [η32_eq]; norm_num [capF])
    have hh := A32.of_exact f32_isFinite_0p5
    rw [f32_toReal_0p5] at hh
    have hm1 := A32.mul hdv hh (by
      simp only [u32]; rw [η32_eq]; norm_num [capF])
    have hsqo := A32.mul hoo hoo (by norm_num [capF])
    have hden := A32.mul ht2 h15 (by norm_num [capF])
    have hq := A32.div hsqo hden (m := 2) (by norm_num) (by
      simp only [u32]; rw [η32_eq]; norm_num) (by
      simp only [u32]; rw [η32_eq]; norm_num [capF])
    have hs := A32.add hm1 hq (by
      simp only [u32]; rw [η32_eq]; norm_num [capF])
    simp only [sq_float, id_run_eq, id_pure_eq]
    refine ⟨hs.1, ?_⟩
    have := hs.2
    rw [ho1]
    have hη := η32_small
    have hη0 := η32_pos
    generalize η32 = η at this hη hη0 ⊢
    simp only [u32] at this
    norm_num at this ⊢
    linarith

/-! ## The horizontal stopping point -/

theorem f32_isFinite_toFloat32_0 (hL : LibmSpec) :
    (Float.toFloat32 0.0).IsFinite ∧ (Float.toFloat32 0.0).toReal = 0 := by
  obtain ⟨f, e⟩ := hL.f64ToF32_exact 0.0 0.0 f64_isFinite_0p0 f32_isFinite_0p0
    (by rw [f32_toReal_0p0, f64_toReal_0p0])
  exact ⟨f, by rw [e, f64_toReal_0p0]⟩

/-- A square of a finite `float` is finite and nonnegative. -/
theorem sq_nonneg32 {a : Float32} (ha : a.IsFinite) (hb : |a.toReal| ≤ 2 ^ (40 : ℤ)) :
    (a * a).IsFinite ∧ 0 ≤ (a * a).toReal ∧ (a * a).toReal ≤ a.toReal ^ 2 * (1 + u32) + η32 := by
  have hm : |a.toReal * a.toReal| ≤ maxFinite32 := by
    rw [abs_mul]
    have : |a.toReal| * |a.toReal| ≤ 2 ^ (40 : ℤ) * 2 ^ (40 : ℤ) :=
      mul_le_mul hb hb (abs_nonneg _) (by positivity)
    have h80 : (2 : ℝ) ^ (40 : ℤ) * 2 ^ (40 : ℤ) ≤ capF := by
      rw [← zpow_add₀ two_ne_zero]; exact zpow_le_zpow_right₀ one_le_two (by norm_num)
    linarith [capF_le_max32]
  obtain ⟨hf, he⟩ := Float32.mul_err_all ha ha hm
  refine ⟨hf, ((Float32.mul_bracket ha ha hm Float32.isFinite_zero).1
    (by rw [Float32.toReal_zero]; nlinarith)).trans_eq' Float32.toReal_zero.symm, ?_⟩
  have h := rnd32 he
  rw [abs_mul_self, ← sq] at h
  have := (abs_le.1 h).2
  nlinarith [sq_nonneg a.toReal]

/-- The sum of two such squares. -/
theorem sumsq_nonneg32 {a b : Float32} (ha : a.IsFinite) (hb : b.IsFinite)
    (ha' : |a.toReal| ≤ 2 ^ (40 : ℤ)) (hb' : |b.toReal| ≤ 2 ^ (40 : ℤ)) :
    (a * a + b * b).IsFinite ∧ 0 ≤ (a * a + b * b).toReal := by
  obtain ⟨fa, na, la⟩ := sq_nonneg32 ha ha'
  obtain ⟨fb, nb, lb⟩ := sq_nonneg32 hb hb'
  have hm : |(a * a).toReal + (b * b).toReal| ≤ maxFinite32 := by
    have h1 : a.toReal ^ 2 ≤ 2 ^ (80 : ℤ) := by
      have := pow_le_pow_left₀ (abs_nonneg _) ha' 2
      rw [sq_abs] at this; norm_num at this ⊢; linarith
    have h2 : b.toReal ^ 2 ≤ 2 ^ (80 : ℤ) := by
      have := pow_le_pow_left₀ (abs_nonneg _) hb' 2
      rw [sq_abs] at this; norm_num at this ⊢; linarith
    have h3 : (2 : ℝ) ^ (80 : ℤ) * 4 + 1 ≤ capF := by norm_num [capF]
    have hu : u32 ≤ 1 := by norm_num [u32]
    have hη := η32_small
    rw [abs_of_nonneg (by linarith)]
    nlinarith [capF_le_max32]
  obtain ⟨hf, -⟩ := Float32.add_err_all fa fb hm
  refine ⟨hf, ((Float32.add_bracket fa fb hm Float32.isFinite_zero).1
    (by rw [Float32.toReal_zero]; linarith)).trans_eq' Float32.toReal_zero.symm⟩

/-- The error budget of one axis of the stopping point. -/
theorem stop_axis_comb {r P m V T px vx : ℝ} (hT0 : 0 ≤ T) (hT1 : T ≤ 1)
    (h1 : |r - (P + m)| ≤ u64 * |P + m| + η64) (h2 : |P - px| ≤ u64 * |px| + η64)
    (h3 : |m - V * T| ≤ u32 * |V * T| + η32) (h4 : |V - vx| ≤ u32 * |vx| + η32) :
    |r - (px + T * vx)| ≤ 1 / 2 ^ 20 * (|px| + |vx|) + 1 / 2 ^ 100 := by
  have hu32 : u32 = 1 / 16777216 := by norm_num [u32]
  have hu64 : u64 = 1 / 9007199254740992 := by norm_num [u64]
  rw [hu32] at h3 h4
  rw [hu64] at h1 h2
  have e32 := η32_small
  have e64 := η64_small
  have p32 := η32_pos
  have p64 := η64_pos
  have hV : |V| ≤ |vx| + (1 / 16777216 * |vx| + η32) := by
    have := abs_sub_abs_le_abs_sub V vx; linarith
  have hVT : |V * T| ≤ |V| := by
    rw [abs_mul, abs_of_nonneg hT0]
    exact mul_le_of_le_one_right (abs_nonneg _) hT1
  have hm : |m| ≤ |V| + (1 / 16777216 * |V| + η32) := by
    have := abs_sub_abs_le_abs_sub m (V * T); linarith
  have hP : |P| ≤ |px| + (1 / 9007199254740992 * |px| + η64) := by
    have := abs_sub_abs_le_abs_sub P px; linarith
  have hPm : |P + m| ≤ |P| + |m| := abs_add_le _ _
  have hTV : T * |V - vx| ≤ 1 / 16777216 * |vx| + η32 := by
    calc T * |V - vx| ≤ 1 * |V - vx| :=
          mul_le_mul_of_nonneg_right hT1 (abs_nonneg _)
      _ ≤ _ := by linarith
  have key : r - (px + T * vx) = (r - (P + m)) + (P - px) + (m - V * T) + T * (V - vx) := by ring
  rw [key]
  have t1 := abs_add_le ((r - (P + m)) + (P - px) + (m - V * T)) (T * (V - vx))
  have t2 := abs_add_le ((r - (P + m)) + (P - px)) (m - V * T)
  have t3 := abs_add_le (r - (P + m)) (P - px)
  rw [abs_mul, abs_of_nonneg hT0] at t1
  have a1 : (0 : ℝ) ≤ |px| := abs_nonneg _
  have a2 : (0 : ℝ) ≤ |vx| := abs_nonneg _
  have a3 : (0 : ℝ) ≤ |V| := abs_nonneg _
  linarith

/-- **The horizontal stopping point** (`AC_PosControl::get_stopping_point_NE_m`) with
`PSC_NE_POS_P = 1.5`, the navigator's `WP_SPD = 1` and `WP_ACC = 1.5`, zero offsets, and finite
estimates (position at most `100` m, velocity at most `10` m/s per axis): there is a time
`0 ≤ T ≤ ⅔ (1 + 2⁻¹⁹)` such that the point is the position estimate plus `T` times the velocity
estimate, up to `2⁻²⁰ (|p| + |v|) + 2⁻¹⁰⁰` per axis. -/
theorem stop_NE_bound (hL : LibmSpec) (p : AC_PosControl.Params) (s : AC_PosControl.State)
    (q : Vector2p.State) (hkp : p._p_pos_ne_m._kp = 1.5) (hacc : s._accel_max_ne_mss = 1.5)
    (hvm : s._vel_max_ne_ms = 1)
    (hpox : A64 s._pos_offset_ned_m.x 0 0) (hpoy : A64 s._pos_offset_ned_m.y 0 0)
    (hvox : A32 s._vel_offset_ned_ms.x 0 0) (hvoy : A32 s._vel_offset_ned_ms.y 0 0)
    (hpx : s._pos_estimate_ned_m.x.IsFinite) (hpy : s._pos_estimate_ned_m.y.IsFinite)
    (hpx' : |s._pos_estimate_ned_m.x.toReal| ≤ 100) (hpy' : |s._pos_estimate_ned_m.y.toReal| ≤ 100)
    (hvx : s._vel_estimate_ned_ms.x.IsFinite) (hvy : s._vel_estimate_ned_ms.y.IsFinite)
    (hvx' : |s._vel_estimate_ned_ms.x.toReal| ≤ 10) (hvy' : |s._vel_estimate_ned_ms.y.toReal| ≤ 10) :
    ∃ T : ℝ, 0 ≤ T ∧ T ≤ 2 / 3 * (1 + (1 / 2 ^ 19 : ℝ)) ∧
      |(AC_PosControl.get_stopping_point_NE_m p s q).x.toReal -
          (s._pos_estimate_ned_m.x.toReal + T * s._vel_estimate_ned_ms.x.toReal)| ≤
        (1 / 2 ^ 20 : ℝ) * (|s._pos_estimate_ned_m.x.toReal| + |s._vel_estimate_ned_ms.x.toReal|) +
          (1 / 2 ^ 100 : ℝ) ∧
      |(AC_PosControl.get_stopping_point_NE_m p s q).y.toReal -
          (s._pos_estimate_ned_m.y.toReal + T * s._vel_estimate_ned_ms.y.toReal)| ≤
        (1 / 2 ^ 20 : ℝ) * (|s._pos_estimate_ned_m.y.toReal| + |s._vel_estimate_ned_ms.y.toReal|) +
          (1 / 2 ^ 100 : ℝ) := by
  simp only [AC_PosControl.get_stopping_point_NE_m, Vector2p.op_sub_assign, Vector2f.op_sub_assign,
    Vector3p.xy, Vector3f.xy, Vector2f.length, norm_float2, sq_float, Vector2p.op_add_assign,
    Vector2f.todouble, Vector2f.op_mul_float, Vector2f.init_float2, Vector2p.init_double2,
    stopping_distance, Id.run, id_pure_eq, hkp, hacc, hvm]
  -- the operands
  have hη32 := η32_small
  have hη64 := η64_small
  have hη0 := η32_pos
  have hη0' := η64_pos
  have hu32 : u32 = 1 / 16777216 := by norm_num [u32]
  have hu64 : u64 = 1 / 9007199254740992 := by norm_num [u64]
  have aPx := A64.sub (A64.of_exact hpx) hpox (by
    simp only [sub_zero, add_zero, capF]; norm_num; linarith)
  have aPy := A64.sub (A64.of_exact hpy) hpoy (by
    simp only [sub_zero, add_zero, capF]; norm_num; linarith)
  have aVx := A32.sub (A32.of_exact hvx) hvox (by
    simp only [sub_zero, add_zero, capF]; norm_num; linarith)
  have aVy := A32.sub (A32.of_exact hvy) hvoy (by
    simp only [sub_zero, add_zero, capF]; norm_num; linarith)
  simp only [sub_zero, add_zero, zero_add] at aPx aPy aVx aVy
  generalize s._pos_estimate_ned_m.x - s._pos_offset_ned_m.x = Px at aPx ⊢
  generalize s._pos_estimate_ned_m.y - s._pos_offset_ned_m.y = Py at aPy ⊢
  generalize s._vel_estimate_ned_ms.x - s._vel_offset_ned_ms.x = Vx at aVx ⊢
  generalize s._vel_estimate_ned_ms.y - s._vel_offset_ned_ms.y = Vy at aVy ⊢
  set px := s._pos_estimate_ned_m.x.toReal with hpxd
  set py := s._pos_estimate_ned_m.y.toReal with hpyd
  set vx := s._vel_estimate_ned_ms.x.toReal with hvxd
  set vy := s._vel_estimate_ned_ms.y.toReal with hvyd
  -- the early returns: `T = 0`
  have base_x : |Px.toReal - px| ≤ (1 / 2 ^ 20 : ℝ) * (|px| + |vx|) + (1 / 2 ^ 100 : ℝ) := by
    have := aPx.2
    rw [hu64] at this
    have h5 : (0 : ℝ) ≤ |vx| := abs_nonneg _
    have h6 : (0 : ℝ) ≤ |px| := abs_nonneg _
    norm_num at this ⊢
    linarith [hη64]
  have base_y : |Py.toReal - py| ≤ (1 / 2 ^ 20 : ℝ) * (|py| + |vy|) + (1 / 2 ^ 100 : ℝ) := by
    have := aPy.2
    rw [hu64] at this
    have h5 : (0 : ℝ) ≤ |vy| := abs_nonneg _
    have h6 : (0 : ℝ) ≤ |py| := abs_nonneg _
    norm_num at this ⊢
    linarith [hη64]
  -- the speed
  have hVx' : |Vx.toReal| ≤ 2 ^ (40 : ℤ) := by
    have := aVx.abs_le; rw [hu32] at this; norm_num at this ⊢; nlinarith [hη32]
  have hVy' : |Vy.toReal| ≤ 2 ^ (40 : ℤ) := by
    have := aVy.abs_le; rw [hu32] at this; norm_num at this ⊢; nlinarith [hη32]
  obtain ⟨fsum, nsum⟩ := sumsq_nonneg32 aVx.1 aVy.1 hVx' hVy'
  have hsum_le : (Vx * Vx + Vy * Vy).toReal ≤ maxFinite32 :=
    (le_abs_self _).trans (Float32.abs_toReal_le_maxFinite _)
  obtain ⟨fS, -⟩ := Float32.sqrt_err_all fsum nsum hsum_le
  generalize hSd : (Vx * Vx + Vy * Vy).sqrt = S at fS ⊢
  -- `S ≥ 0` and `S ≤ 15`
  have hS0 : 0 ≤ S.toReal := by
    rw [← hSd]
    have := (Float32.sqrt_bracket fsum nsum hsum_le Float32.isFinite_zero).1
      (by rw [Float32.toReal_zero]; exact Real.sqrt_nonneg _)
    rwa [Float32.toReal_zero] at this
  -- the clamp and the stopping distance
  obtain ⟨f0, e0⟩ := f32_isFinite_toFloat32_0 hL
  obtain ⟨fO, eO⟩ := constrain_spec (Int32.toUInt32 1401) fS f0 Float32.isFinite_one
    (by rw [e0, Float32.toReal_one]; norm_num)
  rw [e0, Float32.toReal_one, max_eq_right (le_min (by norm_num) hS0)] at eO
  generalize constrain_value_line_float S (Float.toFloat32 0.0) 1 (Int32.toUInt32 1401) = O at fO eO ⊢
  have hO0 : 0 ≤ O.toReal := by rw [eO]; exact le_min (by norm_num) hS0
  have hO1 : O.toReal ≤ 1 := by rw [eO]; exact min_le_left _ _
  have hOS : O.toReal ≤ S.toReal := by rw [eO]; exact min_le_right _ _
  obtain ⟨fD, eD⟩ := invSqrt_15 hL fO hO0 hO1
  generalize inv_sqrt_controller O 1.5 1.5 = D at fD eD ⊢
  by_cases hSp : is_positive_float S = true
  swap
  · simp only [hSp, Bool.not_false, ite_true]
    exact ⟨0, le_refl _, by positivity, by simpa using base_x, by simpa using base_y⟩
  by_cases hDp : is_positive_float D = true
  swap
  · simp only [hSp, hDp, Bool.not_false, Bool.not_true, Bool.false_eq_true, ite_true, ite_false]
    exact ⟨0, le_refl _, by positivity, by simpa using base_x, by simpa using base_y⟩
  simp only [hSp, hDp, Bool.not_true, Bool.false_eq_true, ite_false]
  have hSl := (isPos_iff fS).1 hSp
  have hDl := (isPos_iff fD).1 hDp
  have hS23 : (1 / 8388608 : ℝ) ≤ S.toReal := by norm_num at hSl ⊢; linarith
  have hD23 : (1 / 8388608 : ℝ) ≤ D.toReal := by norm_num at hDl ⊢; linarith
  -- the time `T = D / S`
  have hSpos : 0 < S.toReal := by linarith
  have hDS : D.toReal / S.toReal ≤ 2 / 3 + 1 / 2 ^ 20 + 1 / 2 ^ 90 := by
    rw [div_le_iff₀ hSpos]
    have hη := η32_small
    have h1 : D.toReal ≤ O.toReal * (2 / 3) + O.toReal / 2 ^ 20 + η32 := by
      have := (abs_le.1 eD).2; norm_num at this ⊢; linarith
    have h2 : η32 ≤ S.toReal / 2 ^ 90 := by
      have : (1 / 10 ^ 40 : ℝ) ≤ (1 / 8388608) / 2 ^ 90 := by norm_num
      have : (1 / 8388608 : ℝ) / 2 ^ 90 ≤ S.toReal / 2 ^ 90 := by gcongr
      linarith
    linarith
  have hDS0 : 0 ≤ D.toReal / S.toReal := div_nonneg (by linarith) hSpos.le
  have hq : |D.toReal / S.toReal| ≤ maxFinite32 := by
    rw [abs_of_nonneg hDS0]
    have : (2 / 3 + 1 / 2 ^ 20 + 1 / 2 ^ 90 : ℝ) ≤ capF := by norm_num [capF]
    linarith [capF_le_max32]
  obtain ⟨fT, eT⟩ := Float32.div_err_all fD fS hSpos.ne' hq
  have hT0 : 0 ≤ (D / S).toReal := by
    have := (Float32.div_bracket fD fS hSpos.ne' hq Float32.isFinite_zero).1
      (by rw [Float32.toReal_zero]; exact hDS0)
    rwa [Float32.toReal_zero] at this
  have hT1 : (D / S).toReal ≤ 2 / 3 * (1 + 1 / 2 ^ 19) := by
    have := (abs_le.1 eT).2
    rw [abs_of_nonneg hDS0] at this
    norm_num at this hDS ⊢
    linarith
  generalize D / S = T' at fT hT0 hT1 ⊢
  refine ⟨T'.toReal, hT0, hT1, ?_, ?_⟩
  · -- the north axis
    have hT1' : T'.toReal ≤ 1 := by
      linarith [show (2 / 3 * (1 + 1 / 2 ^ 19) : ℝ) ≤ 1 by norm_num]
    have hVxn : |Vx.toReal| ≤ 2 ^ 40 := by
      have := aVx.abs_le; rw [hu32] at this; norm_num at this ⊢; linarith [η32_small]
    have hVTa : |Vx.toReal * T'.toReal| ≤ |Vx.toReal| := by
      rw [abs_mul, abs_of_nonneg hT0]
      exact mul_le_of_le_one_right (abs_nonneg _) hT1'
    have hVT : |Vx.toReal * T'.toReal| ≤ maxFinite32 := by
      have : (2 : ℝ) ^ 40 ≤ capF := by norm_num [capF]
      linarith [capF_le_max32]
    obtain ⟨fm, em⟩ := Float32.mul_err_all aVx.1 fT hVT
    obtain ⟨fm', em'⟩ := hL.f32ToF64 _ fm
    have hm2 : |(Vx * T').toReal| ≤ 2 ^ 41 := by
      have h1 := abs_sub_abs_le_abs_sub (Vx * T').toReal (Vx.toReal * T'.toReal)
      have h2 := hVTa.trans hVxn
      have h3 := em
      generalize |Vx.toReal * T'.toReal| = w at h1 h2 h3
      norm_num at h2 h3 ⊢
      linarith
    have hPm : |Px.toReal + (Float32.toFloat (Vx * T')).toReal| ≤ maxFinite := by
      rw [em']
      have h1 := aPx.abs_le
      rw [hu64] at h1
      have : |Px.toReal + (Vx * T').toReal| ≤ |Px.toReal| + |(Vx * T').toReal| := abs_add_le _ _
      have : (100 : ℝ) + (100 / 9007199254740992 + 1) + 2 ^ 41 ≤ capF := by norm_num [capF]
      have : 1 / 9007199254740992 * |px| ≤ 100 / 9007199254740992 := by linarith
      linarith [capF_le_max64, η64_small]
    obtain ⟨fr, er⟩ := Float.add_err_all aPx.1 fm' hPm
    rw [em'] at er
    have er' := rnd64 (fl := (Px + Float32.toFloat (Vx * T')).toReal)
      (x := Px.toReal + (Vx * T').toReal)
      (by have : (0 : ℝ) ≤ 2 ^ (-1075 : ℤ) := by positivity
          linarith)
    exact stop_axis_comb hT0 hT1' er' aPx.2 (rnd32 em) aVx.2
  · -- the east axis
    have hT1' : T'.toReal ≤ 1 := by
      linarith [show (2 / 3 * (1 + 1 / 2 ^ 19) : ℝ) ≤ 1 by norm_num]
    have hVyn : |Vy.toReal| ≤ 2 ^ 40 := by
      have := aVy.abs_le; rw [hu32] at this; norm_num at this ⊢; linarith [η32_small]
    have hVTa : |Vy.toReal * T'.toReal| ≤ |Vy.toReal| := by
      rw [abs_mul, abs_of_nonneg hT0]
      exact mul_le_of_le_one_right (abs_nonneg _) hT1'
    have hVT : |Vy.toReal * T'.toReal| ≤ maxFinite32 := by
      have : (2 : ℝ) ^ 40 ≤ capF := by norm_num [capF]
      linarith [capF_le_max32]
    obtain ⟨fm, em⟩ := Float32.mul_err_all aVy.1 fT hVT
    obtain ⟨fm', em'⟩ := hL.f32ToF64 _ fm
    have hm2 : |(Vy * T').toReal| ≤ 2 ^ 41 := by
      have h1 := abs_sub_abs_le_abs_sub (Vy * T').toReal (Vy.toReal * T'.toReal)
      have h2 := hVTa.trans hVyn
      have h3 := em
      generalize |Vy.toReal * T'.toReal| = w at h1 h2 h3
      norm_num at h2 h3 ⊢
      linarith
    have hPm : |Py.toReal + (Float32.toFloat (Vy * T')).toReal| ≤ maxFinite := by
      rw [em']
      have h1 := aPy.abs_le
      rw [hu64] at h1
      have : |Py.toReal + (Vy * T').toReal| ≤ |Py.toReal| + |(Vy * T').toReal| := abs_add_le _ _
      have : (100 : ℝ) + (100 / 9007199254740992 + 1) + 2 ^ 41 ≤ capF := by norm_num [capF]
      have : 1 / 9007199254740992 * |py| ≤ 100 / 9007199254740992 := by linarith
      linarith [capF_le_max64, η64_small]
    obtain ⟨fr, er⟩ := Float.add_err_all aPy.1 fm' hPm
    rw [em'] at er
    have er' := rnd64 (fl := (Py + Float32.toFloat (Vy * T')).toReal)
      (x := Py.toReal + (Vy * T').toReal)
      (by have : (0 : ℝ) ≤ 2 ^ (-1075 : ℤ) := by positivity
          linarith)
    exact stop_axis_comb hT0 hT1' er' aPy.2 (rnd32 em) aVy.2

/-! ## The vertical stopping point -/

theorem f32_div_1 : (1 : Float32) / 1 = 1 := by decide

/-- `inv_sqrt_controller o 1 1` for `|o| < 1` is `o / 1`. -/
theorem invSqrt_1 (hL : LibmSpec) {o : Float32} (ho : o.IsFinite) (h1 : |o.toReal| < 1) :
    A32 (inv_sqrt_controller o 1 1) o.toReal (u32 * |o.toReal| + η32) := by
  have hn : is_negative_float 1 = false :=
    isNeg_false hL Float32.isFinite_one (by rw [Float32.toReal_one]; norm_num)
  have hz : is_zero_float 1 = false := by decide
  simp only [inv_sqrt_controller, Id.run, hn, hz, f32_div_1, Bool.and_false,
    Bool.false_eq_true, ite_false, Bool.or_false, Bool.not_false, Bool.and_true, id_pure_eq]
  have hab := (Float32.isFinite_abs o).2 ho
  have hlt : Float32.abs o < 1 := by
    rw [Float32.lt_iff_toReal_lt hab Float32.isFinite_one, Float32.toReal_abs, Float32.toReal_one]
    exact h1
  rw [ite_eq_left hlt]
  have hd := A32.div (A32.of_exact ho) (A32.of_exact Float32.isFinite_one) (m := 1 / 2)
    (by norm_num) (by rw [Float32.toReal_one]; norm_num) (by
      rw [Float32.toReal_one]; norm_num [capF]; linarith [abs_nonneg o.toReal])
  rw [Float32.toReal_one] at hd
  simp only [div_one, mul_zero, add_zero, abs_one, zero_add, zero_div] at hd
  exact hd

/-- **The vertical stopping point** (`AC_PosControl::get_stopping_point_D_m`) with
`PSC_D_POS_P = 1`, the navigator's `WP_ACC_Z = 1`, zero offsets, a finite position estimate
(at most `100` m) and a vertical velocity estimate below `1` m/s: the position estimate plus the
velocity, up to `2⁻²⁰ (|p| + |v|) + 2⁻¹⁰⁰` (two roundings of the position to `float`). -/
theorem stop_D_bound (hL : LibmSpec) (p : AC_PosControl.Params) (s : AC_PosControl.State)
    (z0 : Float) (hkp : p._p_pos_d_m._kp = 1) (hacc : s._accel_max_d_mss = 1)
    (hpo : A64 s._pos_offset_ned_m.z 0 0) (hvo : A32 s._vel_offset_ned_ms.z 0 0)
    (hpz : s._pos_estimate_ned_m.z.IsFinite) (hpz' : |s._pos_estimate_ned_m.z.toReal| ≤ 100)
    (hvz : s._vel_estimate_ned_ms.z.IsFinite) (hvz' : |s._vel_estimate_ned_ms.z.toReal| ≤ 9 / 10) :
    |(AC_PosControl.get_stopping_point_D_m p s z0).toReal -
        (s._pos_estimate_ned_m.z.toReal + s._vel_estimate_ned_ms.z.toReal)| ≤
      1 / 2 ^ 20 * (|s._pos_estimate_ned_m.z.toReal| + |s._vel_estimate_ned_ms.z.toReal|) +
        1 / 2 ^ 100 := by
  simp only [AC_PosControl.get_stopping_point_D_m, stopping_distance, Id.run, id_pure_eq, hkp, hacc]
  have c1 : (!is_positive_AP_Float 1 || !is_positive_float 1) = false := by decide
  rw [c1]
  simp only [Bool.false_eq_true, ite_false]
  set pz := s._pos_estimate_ned_m.z.toReal with hpzd
  set vz := s._vel_estimate_ned_ms.z.toReal with hvzd
  have hu32 : u32 = 1 / 16777216 := by norm_num [u32]
  have hu64 : u64 = 1 / 9007199254740992 := by norm_num [u64]
  have e32 := η32_small
  have e64 := η64_small
  have p32 := η32_pos
  have p64 := η64_pos
  -- the position, twice through `float`
  have a1 := (A64.of_exact hpz).toFloat32 hL (by norm_num [capF]; linarith)
  have a2 := (a1.toFloat hL).sub hpo (by
    rw [hu32]; norm_num [capF]; linarith)
  simp only [sub_zero, add_zero, ← hpzd] at a2
  have a3 := a2.toFloat32 hL (by
    rw [hu32, hu64]; norm_num [capF]; linarith)
  -- the velocity
  have b1 := (A32.of_exact hvz).sub hvo (by norm_num [capF]; linarith)
  simp only [sub_zero, add_zero, zero_add, ← hvzd] at b1
  have hb1 : |(s._vel_estimate_ned_ms.z - s._vel_offset_ned_ms.z).toReal| < 1 := by
    have := b1.abs_le; rw [hu32] at this; linarith
  have b2 := invSqrt_1 hL b1.1 hb1
  -- the clamp to `[-3, 2]`
  obtain ⟨fc, ec⟩ := constrain_spec (Int32.toUInt32 1428) b2.1 f32_isFinite_m3p0 f32_isFinite_2p0
    (by rw [f32_toReal_m3p0, f32_toReal_2p0]; norm_num)
  rw [f32_toReal_m3p0, f32_toReal_2p0] at ec
  have hb2 : |(inv_sqrt_controller (s._vel_estimate_ned_ms.z - s._vel_offset_ned_ms.z) 1 1).toReal| ≤ 1 := by
    have h1 := b2.abs_le
    have h2 := b1.abs_le
    rw [hu32] at h1 h2
    have : |(s._vel_estimate_ned_ms.z - s._vel_offset_ned_ms.z).toReal| ≤ 9 / 10 + 1 / 16777216 * (9 / 10) + 1 / 10 ^ 40 := by
      have : 1 / 16777216 * |vz| ≤ 1 / 16777216 * (9 / 10) := by linarith
      linarith
    linarith
  rw [max_eq_right (by rw [abs_le] at hb2; exact le_min (by linarith) (by linarith)),
    min_eq_right (by rw [abs_le] at hb2; linarith)] at ec
  have b3 : A32 (constrain_value_line_float
      (inv_sqrt_controller (s._vel_estimate_ned_ms.z - s._vel_offset_ned_ms.z) 1 1) (-3.0) 2.0
      (Int32.toUInt32 1428)) vz
      ((u32 * |(s._vel_estimate_ned_ms.z - s._vel_offset_ned_ms.z).toReal| + η32) +
        (u32 * |vz| + η32)) :=
    ⟨fc, by rw [ec]; exact (abs_sub_le _ _ _).trans (add_le_add b2.2 b1.2)⟩
  -- the sum and the widening
  have a4 := (a3.add b3 (by
    rw [hu32, hu64]; norm_num [capF]
    have := abs_add_le pz vz
    rw [abs_le] at hpz' hvz'
    have h1 : |pz| ≤ 100 := abs_le.2 hpz'
    have h2 : |vz| ≤ 9 / 10 := abs_le.2 hvz'
    nlinarith [abs_nonneg pz, abs_nonneg vz])).toFloat hL
  have := a4.2
  have hpv := abs_add_le pz vz
  have hb1' := b1.abs_le
  generalize η32 = e at this e32 p32 hb1'
  generalize η64 = f at this e64 p64
  rw [hu32, hu64] at this
  rw [hu32] at hb1'
  norm_num at this ⊢
  have ha : (0 : ℝ) ≤ |pz| := abs_nonneg _
  have hb : (0 : ℝ) ≤ |vz| := abs_nonneg _
  linarith

/-! ## The loiter destination -/

/-- The stopping point `get_wp_stopping_point_NED_m` as a point of `P3`. -/
def stopPt (p : AC_PosControl.Params) (s : AC_PosControl.State) : P3 :=
  !₂[(AC_PosControl.get_stopping_point_NE_m p s {}).x.toReal,
    (AC_PosControl.get_stopping_point_NE_m p s {}).y.toReal,
    (AC_PosControl.get_stopping_point_D_m p s 0.0).toReal]

/-- The position estimate as a point. -/
def estPos (s : AC_PosControl.State) : P3 :=
  !₂[s._pos_estimate_ned_m.x.toReal, s._pos_estimate_ned_m.y.toReal, s._pos_estimate_ned_m.z.toReal]

/-- The velocity estimate as a vector. -/
def estVel (s : AC_PosControl.State) : P3 :=
  !₂[s._vel_estimate_ned_ms.x.toReal, s._vel_estimate_ned_ms.y.toReal, s._vel_estimate_ned_ms.z.toReal]

theorem norm_eq3 (v : P3) : ‖v‖ = Real.sqrt (v 0 ^ 2 + v 1 ^ 2 + v 2 ^ 2) := by
  rw [EuclideanSpace.norm_eq, Fin.sum_univ_three]; simp [sq_abs]

/-- **Milestone (a), the loiter target bound.** Under the hypotheses of `stop_NE_bound` and
`stop_D_bound` with the position estimate within `2` m of the origin per axis, the stopping point is
within `d + ‖v‖ + 10⁻⁵` of any point `c` within `d` of the position estimate. -/
theorem loiter_dest_bound (hL : LibmSpec) (p : AC_PosControl.Params) (s : AC_PosControl.State)
    (hkp : p._p_pos_ne_m._kp = 1.5) (hacc : s._accel_max_ne_mss = 1.5) (hvm : s._vel_max_ne_ms = 1)
    (hkpd : p._p_pos_d_m._kp = 1) (haccd : s._accel_max_d_mss = 1)
    (hpox : A64 s._pos_offset_ned_m.x 0 0) (hpoy : A64 s._pos_offset_ned_m.y 0 0)
    (hpoz : A64 s._pos_offset_ned_m.z 0 0)
    (hvox : A32 s._vel_offset_ned_ms.x 0 0) (hvoy : A32 s._vel_offset_ned_ms.y 0 0)
    (hvoz : A32 s._vel_offset_ned_ms.z 0 0)
    (hpx : s._pos_estimate_ned_m.x.IsFinite) (hpy : s._pos_estimate_ned_m.y.IsFinite)
    (hpz : s._pos_estimate_ned_m.z.IsFinite)
    (hpx' : |s._pos_estimate_ned_m.x.toReal| ≤ 2) (hpy' : |s._pos_estimate_ned_m.y.toReal| ≤ 2)
    (hpz' : |s._pos_estimate_ned_m.z.toReal| ≤ 2)
    (hvx : s._vel_estimate_ned_ms.x.IsFinite) (hvy : s._vel_estimate_ned_ms.y.IsFinite)
    (hvz : s._vel_estimate_ned_ms.z.IsFinite)
    (hv : ‖estVel s‖ ≤ 9 / 10) (c : P3) :
    dist (stopPt p s) c ≤ dist (estPos s) c + ‖estVel s‖ + 1 / 10 ^ 5 := by
  have hv0 := norm_eq3 (estVel s)
  have e0 : estVel s 0 = s._vel_estimate_ned_ms.x.toReal := by simp [estVel]
  have e1 : estVel s 1 = s._vel_estimate_ned_ms.y.toReal := by simp [estVel]
  have e2 : estVel s 2 = s._vel_estimate_ned_ms.z.toReal := by simp [estVel]
  rw [e0, e1, e2] at hv0
  set vx := s._vel_estimate_ned_ms.x.toReal
  set vy := s._vel_estimate_ned_ms.y.toReal
  set vz := s._vel_estimate_ned_ms.z.toReal
  have hvx2 : vx ^ 2 ≤ (9 / 10) ^ 2 := by
    have : Real.sqrt (vx ^ 2 + vy ^ 2 + vz ^ 2) ≤ 9 / 10 := hv0 ▸ hv
    rw [Real.sqrt_le_left (by norm_num)] at this; nlinarith [sq_nonneg vy, sq_nonneg vz]
  have hvy2 : vy ^ 2 ≤ (9 / 10) ^ 2 := by
    have : Real.sqrt (vx ^ 2 + vy ^ 2 + vz ^ 2) ≤ 9 / 10 := hv0 ▸ hv
    rw [Real.sqrt_le_left (by norm_num)] at this; nlinarith [sq_nonneg vx, sq_nonneg vz]
  have hvz2 : vz ^ 2 ≤ (9 / 10) ^ 2 := by
    have : Real.sqrt (vx ^ 2 + vy ^ 2 + vz ^ 2) ≤ 9 / 10 := hv0 ▸ hv
    rw [Real.sqrt_le_left (by norm_num)] at this; nlinarith [sq_nonneg vx, sq_nonneg vy]
  have avx : |vx| ≤ 9 / 10 := abs_le.2 ⟨by nlinarith, by nlinarith⟩
  have avy : |vy| ≤ 9 / 10 := abs_le.2 ⟨by nlinarith, by nlinarith⟩
  have avz : |vz| ≤ 9 / 10 := abs_le.2 ⟨by nlinarith, by nlinarith⟩
  obtain ⟨T, hT0, hT1, ex, ey⟩ := stop_NE_bound hL p s {} hkp hacc hvm hpox hpoy hvox hvoy
    hpx hpy (by linarith) (by linarith) hvx hvy (by linarith) (by linarith)
  have ez := stop_D_bound hL p s 0.0 hkpd haccd hpoz hvoz hpz (by linarith) hvz avz
  set px := s._pos_estimate_ned_m.x.toReal
  set py := s._pos_estimate_ned_m.y.toReal
  set pz := s._pos_estimate_ned_m.z.toReal
  have hT1' : T ≤ 1 := by
    linarith [show (2 / 3 * (1 + 1 / 2 ^ 19) : ℝ) ≤ 1 by norm_num]
  set q : P3 := !₂[px + T * vx, py + T * vy, pz + vz] with hq
  have d1 : dist (stopPt p s) q ≤ 1 / 10 ^ 5 := by
    refine (dist_le_sum_abs _ _).trans ?_
    have q0 : q 0 = px + T * vx := by simp [hq]
    have q1 : q 1 = py + T * vy := by simp [hq]
    have q2 : q 2 = pz + vz := by simp [hq]
    have s0 : stopPt p s 0 = (AC_PosControl.get_stopping_point_NE_m p s {}).x.toReal := by
      simp [stopPt]
    have s1 : stopPt p s 1 = (AC_PosControl.get_stopping_point_NE_m p s {}).y.toReal := by
      simp [stopPt]
    have s2 : stopPt p s 2 = (AC_PosControl.get_stopping_point_D_m p s 0.0).toReal := by
      simp [stopPt]
    rw [q0, q1, q2, s0, s1, s2]
    have : 1 / 2 ^ 20 * (|px| + |vx|) + 1 / 2 ^ 100 ≤ (1 / 2 ^ 20 * (2 + 9 / 10) + 1 / 2 ^ 100 : ℝ) := by
      gcongr
    have : 1 / 2 ^ 20 * (|py| + |vy|) + 1 / 2 ^ 100 ≤ (1 / 2 ^ 20 * (2 + 9 / 10) + 1 / 2 ^ 100 : ℝ) := by
      gcongr
    have : 1 / 2 ^ 20 * (|pz| + |vz|) + 1 / 2 ^ 100 ≤ (1 / 2 ^ 20 * (2 + 9 / 10) + 1 / 2 ^ 100 : ℝ) := by
      gcongr
    have : 3 * (1 / 2 ^ 20 * (2 + 9 / 10) + 1 / 2 ^ 100 : ℝ) ≤ 1 / 10 ^ 5 := by norm_num
    linarith
  have d2 : dist q (estPos s) ≤ ‖estVel s‖ := by
    rw [dist_eq3, hv0]
    have q0 : q 0 = px + T * vx := by simp [hq]
    have q1 : q 1 = py + T * vy := by simp [hq]
    have q2 : q 2 = pz + vz := by simp [hq]
    have p0 : estPos s 0 = px := by simp [estPos, px]
    have p1 : estPos s 1 = py := by simp [estPos, py]
    have p2 : estPos s 2 = pz := by simp [estPos, pz]
    rw [q0, q1, q2, p0, p1, p2]
    apply Real.sqrt_le_sqrt
    have hT2 : T ^ 2 ≤ 1 := by nlinarith
    nlinarith [sq_nonneg vx, sq_nonneg vy, mul_le_mul_of_nonneg_right hT2 (sq_nonneg vx),
      mul_le_mul_of_nonneg_right hT2 (sq_nonneg vy)]
  have := dist_triangle4 (stopPt p s) q (estPos s) c
  linarith

/-- With the rest condition of `ψnavA` at the completion tick (sampled position within
`δs + rRest` of `w7`, sampled speed at most `rRest + δv`), the loiter destination is within `ρ` of
`w7`: `0.096 + 0.001 + 0.056 + 10⁻⁵ = 0.15301 ≤ 0.155`. -/
theorem loiter_dest_near_w7 (hL : LibmSpec) (p : AC_PosControl.Params) (s : AC_PosControl.State)
    (hkp : p._p_pos_ne_m._kp = 1.5) (hacc : s._accel_max_ne_mss = 1.5) (hvm : s._vel_max_ne_ms = 1)
    (hkpd : p._p_pos_d_m._kp = 1) (haccd : s._accel_max_d_mss = 1)
    (hpox : A64 s._pos_offset_ned_m.x 0 0) (hpoy : A64 s._pos_offset_ned_m.y 0 0)
    (hpoz : A64 s._pos_offset_ned_m.z 0 0)
    (hvox : A32 s._vel_offset_ned_ms.x 0 0) (hvoy : A32 s._vel_offset_ned_ms.y 0 0)
    (hvoz : A32 s._vel_offset_ned_ms.z 0 0)
    (hpx : s._pos_estimate_ned_m.x.IsFinite) (hpy : s._pos_estimate_ned_m.y.IsFinite)
    (hpz : s._pos_estimate_ned_m.z.IsFinite)
    (hvx : s._vel_estimate_ned_ms.x.IsFinite) (hvy : s._vel_estimate_ned_ms.y.IsFinite)
    (hvz : s._vel_estimate_ned_ms.z.IsFinite)
    (hd : dist (estPos s) w7 ≤ δs + rRest) (hv : ‖estVel s‖ ≤ rRest + δv) :
    dist (stopPt p s) w7 ≤ ρ := by
  have hc : ∀ i : Fin 3, |estPos s i| ≤ 2 := by
    intro i
    have h1 := abs_coord_le_dist (estPos s) w7 i
    have h2 : |w7 i| ≤ 1 := by fin_cases i <;> norm_num [w7, wp]
    have h3 := abs_sub_abs_le_abs_sub (estPos s i) (w7 i)
    norm_num [δs, rRest] at hd
    linarith
  have c0 := hc 0
  have c1 := hc 1
  have c2 := hc 2
  simp [estPos] at c0 c1 c2
  have h := loiter_dest_bound hL p s hkp hacc hvm hkpd haccd hpox hpoy hpoz hvox hvoy hvoz hpx hpy
    hpz c0 c1 c2 hvx hvy hvz (by norm_num [rRest, δv] at hv ⊢; linarith) w7
  norm_num [δs, rRest, δv, ρ] at hd hv ⊢
  linarith

end

end Contracts.Mission
