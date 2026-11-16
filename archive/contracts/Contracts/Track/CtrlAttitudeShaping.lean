import Contracts.Track.CtrlAttitudeBase
import FloatModel.Lit

/-!
# C9: the attitude input shaping (`attitude_command_model`), milestone M4

`AC_AttitudeControl::attitude_command_model(e, ψ̇_des, ω, α, max_ang_vel, accel_max, input_tc, dt)`
returns `(ω', α')`: `α' = shape_angle_vel_accel(...)` (the jerk-limited step of
`shape_pos_vel_accel` with `limit_total = true`, through `sqrt_controller`,
`sqrt_controller_accel` and `shape_accel`), and `ω' = ω + α'·dt`. This file reads it as a real law
plus a numeric error (`A32 x r β`: the `float` `x` is finite and within `β` of the real `r`).
`update_attitude_target` (the quaternion integration of `ω`) is not part of this file.

**Constants.** The real laws use exact real constants: `accel_max = 10π` (`radians(1800)`),
`k_v = 1/input_tc = 20`, jerk step `jerk·dt = π/2` for roll/pitch; `3π/2` (`radians(270)`),
`k_v = 1/(10 dt) = 40`, `jerk·dt = 3π/20` and the slew `π/3` (`radians(60)`) for yaw; `dt = 1/400`.
The `float` constants are hypotheses with bounds (`|accel_max − 10π| ≤ 10⁻⁵`, `input_tc` and `dt`
the `float` values `0.05 = 13421773·2⁻²⁸`, `1/400 = 5368709·2⁻³¹`; `radians_1800`, `radians_270`,
`radians_60`, `radians_0` discharge them for the parameters, the `float` π entering through
`pi32`); their deviations from the real constants are absorbed into `β`. `desired_ang_vel`
(roll/pitch) and the zeros `(float) 0.0` of the code are zeros of either sign.

* (c) `rp_accel_invariant`, `yaw_accel_invariant`: **region-free**: for any inputs `e, ψ̇, ω`
  (not even finiteness is needed: the clamps of `shape_pos_vel_accel` are NaN-safe) and a finite
  `α` with `|α| ≤ accel_max + 10⁻⁵` (`accel_max` the real value of the `float`), `α'` is finite,
  `|α'| ≤ accel_max + 10⁻⁵` and `|α' − α| ≤ jerk·dt + 2·10⁻⁵` (`π/2`, resp. `3π/20`).
  `acm_rate_step`: `ω' = ω + α'/400` within `10⁻⁴` for `|ω| ≤ 1000` (`ω'` is not clamped).
* (a) `rp_law_linear`: roll/pitch, `|e| ≤ 0.0785 < π/40`: `α' ≈ rpStep (rpLin σ e ω) α`,
  `α* = 20 (20 e − (1 + σ) ω)`, `β = 10⁻³`; `ω'` within `5·10⁻⁶`.
* (b) `rp_law_sqrt`: roll/pitch, `0.0786 ≤ |e| ≤ 0.3`: `α' ≈ rpStep (rpSq σ e ω) α`,
  `α* = 20 (v_s − ω) − σ (10π/|v_s|) ω`, `v_s = sign(e) √(20π (|e| − π/80))`, `β = 1.2·10⁻²`;
  `ω'` within `4·10⁻⁵`.
* (d) `yaw_law_linear`: yaw, `|e| ≤ 0.0029 < 3π/3200`, both velocity clamps:
  `α* = 40 (clamp(ψ̇ + clamp(40 e − σ (ω − ψ̇), ±π/3), ±π/3) − ω)`, `β = 3.2·10⁻³`; `ω'` within
  `10⁻⁵`.

`σ` is the Boolean `is_positive(vel_corr_cmd · (ω − ψ̇))` of `sqrt_controller_accel`; each law states
it through the real product, up to the error of the `float` product. The errors are dominated by
`wrap_PI` (`wrapPI_near`): `fmodf` is only specified up to the integer multiple
(`LibmSpec.fmodf`), and for `e < 0` the code goes through `e + 2π` and back, which rounds
(`1.4·10⁻⁶` on `e`, times `k_v²`); for `e ≥ 0` the wrap is exact.

**Not exact.** The invariant carries a `10⁻⁵` slack: `|α' − α| ≤ (float)(jerk·dt)` is false in
`float` (with `α = −14.859199523925781`, target `−accel_max`: `α' − α` exceeds the jerk step by
`8.3·10⁻⁷`, the rounding of `α + δ`); `|α'| ≤ accel_max` exactly needs a Sterbenz argument (true
on the floats checked numerically, not proved here).
-/

namespace Contracts.Track.Att

open Float.Model UnpackedFloat Contracts.Mission AC_Attitude_lib

noncomputable section

/-! ## Real clamps -/

/-- The real clamp `max l (min h x)`, the value of `constrain_value(x, l, h)` for `l ≤ h`. -/
def clampR (l h x : ℝ) : ℝ := max l (min h x)

/-- The clamp is `1`-Lipschitz in each argument. -/
theorem clampR_lip (l h x l' h' x' : ℝ) :
    |clampR l h x - clampR l' h' x'| ≤ |l - l'| + |h - h'| + |x - x'| := by
  unfold clampR
  have h1 := abs_max_sub_max_le_max l (min h x) l' (min h' x')
  have h2 := abs_min_sub_min_le_max h x h' x'
  have h3 : max |l - l'| |min h x - min h' x'| ≤ |l - l'| + |min h x - min h' x'| :=
    max_le (by linarith [abs_nonneg (min h x - min h' x')]) (by linarith [abs_nonneg (l - l')])
  have h4 : max |h - h'| |x - x'| ≤ |h - h'| + |x - x'| :=
    max_le (by linarith [abs_nonneg (x - x')]) (by linarith [abs_nonneg (h - h')])
  linarith

theorem clampR_le {l h x : ℝ} (hlh : l ≤ h) : clampR l h x ≤ h :=
  max_le hlh (min_le_left _ _)

theorem le_clampR {l h x : ℝ} : l ≤ clampR l h x := le_max_left _ _

theorem clampR_of_mem {l h x : ℝ} (h1 : l ≤ x) (h2 : x ≤ h) : clampR l h x = x := by
  unfold clampR; rw [min_eq_right h2, max_eq_right h1]

theorem abs_clampR_le {L x : ℝ} (hL : 0 ≤ L) : |clampR (-L) L x| ≤ L :=
  abs_le.2 ⟨le_clampR, clampR_le (by linarith)⟩

/-! ## `A32` helpers -/

theorem A32.recenter {x : Float32} {r r' e d : ℝ} (h : A32 x r e) (hd : |r - r'| ≤ d) :
    A32 x r' (e + d) :=
  ⟨h.1, by
    calc |x.toReal - r'| ≤ |x.toReal - r| + |r - r'| := abs_sub_le _ _ _
      _ ≤ e + d := add_le_add h.2 hd⟩

theorem A32.neg {x : Float32} {r e : ℝ} (h : A32 x r e) : A32 (-x) (-r) e :=
  ⟨(Float32.isFinite_neg x).2 h.1, by
    rw [Float32.toReal_neg, show -x.toReal - -r = -(x.toReal - r) by ring, abs_neg]; exact h.2⟩

theorem A32.of_val {x : Float32} {r : ℝ} (h : x.IsFinite) (hr : x.toReal = r) : A32 x r 0 :=
  ⟨h, by rw [hr, sub_self, abs_zero]⟩

theorem A32.e_nonneg {x : Float32} {r e : ℝ} (h : A32 x r e) : 0 ≤ e := (abs_nonneg _).trans h.2

theorem A32.lo {x : Float32} {r e : ℝ} (h : A32 x r e) : r - e ≤ x.toReal := by
  have := (abs_le.1 h.2).1; linarith

theorem A32.hi {x : Float32} {r e : ℝ} (h : A32 x r e) : x.toReal ≤ r + e := by
  have := (abs_le.1 h.2).2; linarith

/-- `constrain_value` of approximations: the real clamp, the errors add. -/
theorem A32.cvl {amt lo hi : Float32} {r l h ε εl εh : ℝ} (line : UInt32) (ha : A32 amt r ε)
    (hl : A32 lo l εl) (hh : A32 hi h εh) (hlh : lo.toReal ≤ hi.toReal) :
    A32 (constrain_value_line_float amt lo hi line) (clampR l h r) (ε + εl + εh) := by
  obtain ⟨hf, hv⟩ := constrain_spec line ha.1 hl.1 hh.1 hlh
  refine ⟨hf, ?_⟩
  rw [hv]
  have := clampR_lip lo.toReal hi.toReal amt.toReal l h r
  unfold clampR at this ⊢
  linarith [hl.2, hh.2, ha.2]

/-! ## Literals -/

theorem f32_unpack_60p0 : (60.0 : Float32).toModel.unpack = .finite .positive 15728640 (-18) (by decide) := by rfl
theorem f32_toReal_60p0 : (60.0 : Float32).toReal = (60 : ℝ) := by
  rw [Float32.toReal, f32_unpack_60p0]; simp [UnpackedFloat.toReal, Sign.apply]; norm_num
theorem f32_isFinite_60p0 : (60.0 : Float32).IsFinite := by
  rw [Float32.isFinite_iff, f32_unpack_60p0]; rfl

theorem f32_unpack_270p0 : (270.0 : Float32).toModel.unpack = .finite .positive 8847360 (-15) (by decide) := by rfl
theorem f32_toReal_270p0 : (270.0 : Float32).toReal = (270 : ℝ) := by
  rw [Float32.toReal, f32_unpack_270p0]; simp [UnpackedFloat.toReal, Sign.apply]; norm_num
theorem f32_isFinite_270p0 : (270.0 : Float32).IsFinite := by
  rw [Float32.isFinite_iff, f32_unpack_270p0]; rfl

theorem f64_unpack_10p0 : (10.0 : Float).toModel.unpack = .finite .positive 5629499534213120 (-49) (by decide) := by rfl
theorem f64_toReal_10p0 : (10.0 : Float).toReal = (10 : ℝ) := by
  rw [Float.toReal, f64_unpack_10p0]; simp [UnpackedFloat.toReal, Sign.apply]; norm_num
theorem f64_isFinite_10p0 : (10.0 : Float).IsFinite := by
  rw [Float.isFinite_iff, f64_unpack_10p0]; rfl

/-- `(float) 0.0` (`Float.toFloat32 0.0`, opaque): finite, value `0`. -/
theorem zf (hL : LibmSpec) : (Float.toFloat32 (0.0 : Float)).IsFinite ∧ (Float.toFloat32 (0.0 : Float)).toReal = 0 :=
  f32_isFinite_toFloat32_0 hL

/-- `(float) 10.0`: finite, value `10`. -/
theorem tenf (hL : LibmSpec) : (Float.toFloat32 (10.0 : Float)).IsFinite ∧ (Float.toFloat32 (10.0 : Float)).toReal = 10 := by
  obtain ⟨f, e⟩ := hL.f64ToF32_exact 10.0 10.0 f64_isFinite_10p0 f32_isFinite_10p0
    (by rw [f32_toReal_10p0, f64_toReal_10p0])
  exact ⟨f, by rw [e, f64_toReal_10p0]⟩

/-- `(float) 2.0`: finite, value `2`. -/
theorem twof (hL : LibmSpec) : (Float.toFloat32 (2.0 : Float)).IsFinite ∧ (Float.toFloat32 (2.0 : Float)).toReal = 2 := by
  obtain ⟨f, e⟩ := hL.f64ToF32_exact 2.0 2.0 f64_isFinite_2p0 f32_isFinite_2p0
    (by rw [f32_toReal_2p0, f64_toReal_2p0])
  exact ⟨f, by rw [e, f64_toReal_2p0]⟩

theorem pi_bounds : 3.141592 < Real.pi ∧ Real.pi < 3.141593 := ⟨Real.pi_gt_d6, Real.pi_lt_d6⟩

theorem piD_bounds : (3.1415926 : ℝ) < piD ∧ piD < 3.1415927 := by
  constructor <;> norm_num [piD]

theorem piD_pi : |piD - Real.pi| ≤ 1 / 10 ^ 15 := piD_close

/-! ## `radians` -/

/-- `radians(d)` for a finite `d` of value `D ∈ [0, 2000]`: within `4·10⁻⁹ D` (plus `10⁻⁴⁰`) of
`D π / 180`. -/
theorem radians_near (hL : LibmSpec) {d : Float32} {D : ℝ} (hd : d.IsFinite) (hD : d.toReal = D)
    (h0 : 0 ≤ D) (h1 : D ≤ 2000) :
    A32 (radians_float d) (D * Real.pi / 180) (D * (4 / 10 ^ 9) + 1 / 10 ^ 39) := by
  have hp := pi32 hL
  have h180 : A32 (180.0 : Float32) 180 0 := A32.of_val f32_isFinite_180p0 f32_toReal_180p0
  obtain ⟨pb1, pb2⟩ := piD_bounds
  have hη := η32_small
  have hη0 := η32_pos
  have hpe : u32 * piD + η32 ≤ 19 / 10 ^ 8 := by
    simp only [u32]; norm_num; nlinarith
  have hq := A32.div_c (hp.mono hpe) h180 (Ra := 3.1415927) (m := 180) (Q := 3.1415927 / 180)
    (by rw [abs_of_pos (by linarith)]; linarith) (by norm_num) (by norm_num) le_rfl
    (by rw [abs_div, abs_of_pos (by linarith), abs_of_pos (by norm_num)]; gcongr)
    (by norm_num [capF]) (e := 22 / 10 ^ 10) (by norm_num)
  have hdd : A32 d D 0 := A32.of_val hd hD
  have hm := A32.mul hdd hq (by
    rw [abs_mul, abs_of_nonneg h0, abs_div, abs_of_pos (by linarith), abs_of_pos (by norm_num : (0:ℝ) < 180)]
    simp only [capF]; norm_num; nlinarith)
  simp only [radians_float, id_run_eq, id_pure_eq]
  refine A32.mono (A32.recenter hm (r' := D * Real.pi / 180) (d := D * (2 / 10 ^ 17)) ?_) ?_
  · rw [show D * (piD / 180) - D * Real.pi / 180 = D / 180 * (piD - Real.pi) by ring, abs_mul,
      abs_of_nonneg (by positivity)]
    have := piD_pi
    calc D / 180 * |piD - Real.pi| ≤ D / 180 * (1 / 10 ^ 15) := by gcongr
      _ ≤ D * (2 / 10 ^ 17) := by nlinarith
  · rw [abs_of_nonneg h0, abs_mul, abs_of_nonneg h0, abs_div, abs_of_pos (by linarith),
      abs_of_pos (by norm_num : (0:ℝ) < 180)]
    simp only [u32]
    norm_num
    nlinarith

/-! ## `wrap_PI` on `[-3, 3]` -/

/-- `wrap_PI(x)` for `|x| ≤ 3`: within `1.4·10⁻⁶` of `x`, and exactly `x` for `x ≥ 0`. (`fmodf` is
only specified up to the integer multiple, `LibmSpec.fmodf`; for `x < 0` the result goes through
`x + 2π` and back, which rounds.) -/
theorem wrapPI_near (hL : LibmSpec) {x : Float32} (hx : x.IsFinite) (h3 : |x.toReal| ≤ 3) :
    A32 (wrap_PI_float x) x.toReal (14 / 10 ^ 7) ∧
      (0 ≤ x.toReal → (wrap_PI_float x).toReal = x.toReal) := by
  have hp := pi32 hL
  obtain ⟨pb1, pb2⟩ := piD_bounds
  have hη := η32_small
  have hη0 := η32_pos
  have hpe : u32 * piD + η32 ≤ 19 / 10 ^ 8 := by simp only [u32]; norm_num; nlinarith
  have hP := hp.mono hpe
  have hPlo := A32.lo hP
  have hPhi := A32.hi hP
  obtain ⟨d2, hd2f, hd2⟩ := Float32.exists_double hp.1 (by
    rw [abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
    have := Float32.abs_toReal_le_maxFinite (Float.toFloat32 (3.1415926535897931 : Float))
    have : |(Float.toFloat32 (3.1415926535897931 : Float)).toReal| ≤ 4 := by
      rw [abs_le]; constructor <;> linarith
    have := capF_le_max32; simp only [capF] at this; norm_num at this ⊢; linarith)
  obtain ⟨hBf, hBv⟩ := Float32.mul_exact hp.1 Float32.isFinite_int32_two hd2f
    (by rw [Float32.toReal_int32_two, hd2]; ring)
  have hBv' : (Float.toFloat32 (3.1415926535897931 : Float) * Int32.toFloat32 2).toReal =
      2 * (Float.toFloat32 (3.1415926535897931 : Float)).toReal := hBv.trans hd2
  -- `(float)(M_PI * 2)`
  have h2d : A64 (3.1415926535897931 * Int32.toFloat 2 : Float) (2 * piD) (1 / 10 ^ 15) := by
    have hm := A64.mul (A64.of_exact f64_isFinite_3p1415926535897931) (A64.of_exact Float.two64.1)
      (by rw [Float.two64.2, f64_toReal_3p1415926535897931]; simp only [capF]; norm_num)
    rw [Float.two64.2, f64_toReal_3p1415926535897931] at hm
    refine (hm.congr (by simp only [piD]; ring)).mono ?_
    have := η64_small; simp only [u64]; norm_num; linarith
  have hD := A64.toFloat32 hL h2d (by rw [abs_of_pos (by linarith)]; simp only [capF]; norm_num; linarith)
  have hD' : A32 (Float.toFloat32 (3.1415926535897931 * Int32.toFloat 2 : Float)) (2 * piD)
      (38 / 10 ^ 8) := hD.mono (by
    rw [abs_of_pos (by linarith)]; simp only [u32]; norm_num; nlinarith)
  obtain ⟨hrf, hrlt, n, hn⟩ := hL.fmodf x _ hx hBf (by rw [hBv']; linarith)
  rw [hBv'] at hrlt hn
  rw [abs_of_pos (show (0:ℝ) < 2 * (Float.toFloat32 (3.1415926535897931 : Float)).toReal by linarith)] at hrlt
  have hrlt' := abs_lt.1 hrlt
  have hz0 := Float32.isFinite_int32_zero
  have hz0v := Float32.toReal_int32_zero
  simp only [wrap_PI_float, wrap_2PI_float, Id.run, id_pure_eq]
  generalize CppLibm.fmodf x (Float.toFloat32 3.1415926535897931 * Int32.toFloat32 2) = res at hrf hrlt hrlt' hn ⊢
  generalize hB : Float.toFloat32 3.1415926535897931 * Int32.toFloat32 2 = B at hBf hBv' ⊢
  generalize Float.toFloat32 (3.1415926535897931 * Int32.toFloat 2 : Float) = D at hD' ⊢
  generalize hPg : Float.toFloat32 (3.1415926535897931 : Float) = P at hp hP hPlo hPhi hBv' hn hrlt' ⊢
  have key : ∀ a b : ℤ, (a : ℝ) * (2 * P.toReal) < n * (2 * P.toReal) →
      (n : ℝ) * (2 * P.toReal) < b * (2 * P.toReal) → a < n ∧ n < b := by
    intro a b h1 h2
    have hP0 : 0 < 2 * P.toReal := by linarith
    exact ⟨by exact_mod_cast lt_of_mul_lt_mul_right h1 hP0.le,
      by exact_mod_cast lt_of_mul_lt_mul_right h2 hP0.le⟩
  have hx3 := abs_le.1 h3
  -- the real value of the result of `wrap_2PI`
  rcases le_or_gt 0 x.toReal with hx0 | hx0
  · -- `x ≥ 0`: `wrap_2PI(x) = x` exactly
    have hr1 : (if res < Int32.toFloat32 0 then res + B else res).IsFinite ∧
        (if res < Int32.toFloat32 0 then res + B else res).toReal = x.toReal := by
      by_cases hneg : res < Int32.toFloat32 0
      · rw [ite_eq_left hneg]
        have hr0 := (Float32.lt_iff_toReal_lt hrf hz0).1 hneg
        rw [hz0v] at hr0
        obtain ⟨hn1', hn2'⟩ := key 0 2 (by push_cast; linarith) (by push_cast; linarith)
        have : n = 1 := by omega
        subst this
        exact Float32.add_exact hrf hBf hx (by rw [hn, hBv']; push_cast; ring)
      · rw [ite_eq_right hneg]
        have hr0 : 0 ≤ res.toReal := by
          have := (Float32.lt_iff_toReal_lt hrf hz0).not.1 hneg
          rw [hz0v] at this; linarith
        obtain ⟨hn1', hn2'⟩ := key (-1) 1 (by push_cast; linarith) (by push_cast; linarith)
        have : n = 0 := by omega
        subst this
        exact ⟨hrf, by rw [hn]; simp⟩
    generalize (if res < Int32.toFloat32 0 then res + B else res) = r1 at hr1 ⊢
    have hng : ¬ r1 > P := by
      rw [gt_iff_lt, Float32.lt_iff_toReal_lt hp.1 hr1.1, hr1.2]; linarith
    rw [ite_eq_right hng]
    exact ⟨⟨hr1.1, by rw [hr1.2]; norm_num⟩, fun _ => hr1.2⟩
  · -- `x < 0`: `wrap_2PI(x) ≈ x + 2π`
    have hr1 : A32 (if res < Int32.toFloat32 0 then res + B else res) (x.toReal + 2 * piD)
        (76 / 10 ^ 8) := by
      by_cases hneg : res < Int32.toFloat32 0
      · rw [ite_eq_left hneg]
        have hr0 := (Float32.lt_iff_toReal_lt hrf hz0).1 hneg
        rw [hz0v] at hr0
        obtain ⟨hn1', hn2'⟩ := key (-1) 1 (by push_cast; linarith) (by push_cast; linarith)
        have : n = 0 := by omega
        subst this
        have hres : A32 res x.toReal 0 := A32.of_val hrf (by rw [hn]; simp)
        have hBa : A32 B (2 * piD) (38 / 10 ^ 8) := ⟨hBf, by
          rw [hBv', show 2 * P.toReal - 2 * piD = 2 * (P.toReal - piD) by ring, abs_mul,
            abs_of_pos (by norm_num : (0:ℝ) < 2)]
          linarith [hP.2]⟩
        exact A32.add_c hres hBa (R := 63 / 10) (by rw [abs_le]; constructor <;> linarith)
          (by simp only [capF]; norm_num) (by norm_num)
      · rw [ite_eq_right hneg]
        have hr0 : 0 ≤ res.toReal := by
          have := (Float32.lt_iff_toReal_lt hrf hz0).not.1 hneg
          rw [hz0v] at this; linarith
        obtain ⟨hn1', hn2'⟩ := key (-2) 0 (by push_cast; linarith) (by push_cast; linarith)
        have : n = -1 := by omega
        subst this
        refine ⟨hrf, ?_⟩
        rw [hn, show x.toReal - ((-1 : ℤ) : ℝ) * (2 * P.toReal) - (x.toReal + 2 * piD) =
          2 * (P.toReal - piD) by push_cast; ring, abs_mul, abs_of_pos (by norm_num : (0:ℝ) < 2)]
        linarith [hP.2]
    generalize (if res < Int32.toFloat32 0 then res + B else res) = r1 at hr1 ⊢
    have hgt : r1 > P := by
      rw [gt_iff_lt, Float32.lt_iff_toReal_lt hp.1 hr1.1]; linarith [A32.lo hr1]
    rw [ite_eq_left hgt]
    have hs := A32.sub_c hr1 hD' (R := 3) (by
      rw [show x.toReal + 2 * piD - 2 * piD = x.toReal by ring]; exact h3)
      (by simp only [capF]; norm_num) (e := 14 / 10 ^ 7) (by norm_num)
    refine ⟨hs.congr (by ring), fun h => absurd h (by linarith)⟩

/-! ## The structure of `shape_pos_vel_accel` and `shape_accel` -/

/-- `shape_accel` with a positive jerk limit and time step: one jerk-limited step. -/
theorem shape_accel_eq {T a j dt : Float32} (hj : is_positive_float j = true)
    (hd : is_positive_float dt = true) :
    shape_accel T a j dt =
      a + constrain_value_line_float (T - a) (-j * dt) (j * dt) (Int32.toUInt32 139) := by
  simp only [shape_accel, Id.run, hj, hd, Bool.not_true, Bool.false_eq_true, ite_false, ite_true,
    id_pure_eq]

/-- The acceleration target of `shape_pos_vel_accel` without velocity limits (roll and pitch),
with the acceleration limit `al` it selects (`-accel_min` or `accel_max`). -/
def tgtRoll (pe vd ad v amin amax j al dt : Float32) : Float32 :=
  let k := j / al
  let V0 := sqrt_controller_float4 pe k al dt
  let V1 := V0 + sqrt_controller_accel pe V0 (v - vd) k al / k
  constrain_value_line_float
    (constrain_value_line_float ((vd + V1 - v) * k) amin amax (Int32.toUInt32 334) + ad)
    amin amax (Int32.toUInt32 341)

/-- The acceleration target of `shape_pos_vel_accel` with both velocity limits active and
`limit_total` (yaw). -/
def tgtYaw (pe vd ad v vmin vmax amin amax j al dt : Float32) : Float32 :=
  let k := j / al
  let V0 := sqrt_controller_float4 pe k al dt
  let V1 := V0 + sqrt_controller_accel pe V0 (v - vd) k al / k
  let V2 := MIN_float2 (MAX_float2 V1 vmin) vmax
  let vt := MIN_float2 (MAX_float2 (vd + V2) vmin) vmax
  constrain_value_line_float
    (constrain_value_line_float ((vt - v) * k) amin amax (Int32.toUInt32 334) + ad)
    amin amax (Int32.toUInt32 341)

/-- Roll/pitch form: no velocity limit is active (`max_ang_vel = 0`). -/
theorem spva_roll {pd p : Float} {vd ad v a vmin vmax amin amax j dt : Float32}
    (h1 : is_positive_float vmin = false) (h2 : is_negative_float vmax = false)
    (h3 : is_negative_float amin = true) (h4 : is_positive_float amax = true)
    (h5 : is_positive_float j = true) (h6 : is_negative_float vmin = false)
    (h7 : is_positive_float vmax = false) :
    shape_pos_vel_accel pd vd ad p v a vmin vmax amin amax j dt true =
      shape_accel (tgtRoll (Float.toFloat32 (pd - p)) vd ad v amin amax j
        (if is_positive_float (Float.toFloat32 (pd - p)) then -amin else amax) dt) a j dt := by
  simp only [shape_pos_vel_accel, tgtRoll, Id.run, h1, h2, h3, h4, h5, h6, h7, Bool.false_eq_true,
    ite_false, ite_true, id_pure_eq, Bool.or_false, Bool.not_true]
  split <;> rfl

/-- Yaw form: both velocity limits active. -/
theorem spva_yaw {pd p : Float} {vd ad v a vmin vmax amin amax j dt : Float32}
    (h1 : is_positive_float vmin = false) (h2 : is_negative_float vmax = false)
    (h3 : is_negative_float amin = true) (h4 : is_positive_float amax = true)
    (h5 : is_positive_float j = true) (h6 : is_negative_float vmin = true)
    (h7 : is_positive_float vmax = true) :
    shape_pos_vel_accel pd vd ad p v a vmin vmax amin amax j dt true =
      shape_accel (tgtYaw (Float.toFloat32 (pd - p)) vd ad v vmin vmax amin amax j
        (if is_positive_float (Float.toFloat32 (pd - p)) then -amin else amax) dt) a j dt := by
  simp only [shape_pos_vel_accel, tgtYaw, Id.run, h1, h2, h3, h4, h5, h6, h7, Bool.false_eq_true,
    ite_false, ite_true, id_pure_eq, Bool.or_false, Bool.not_true]
  split <;> rfl

/-- Whatever the velocity limits: the result is a jerk-limited step towards a doubly clamped
target. -/
theorem spva_any {pd p : Float} {vd ad v a vmin vmax amin amax j dt : Float32}
    (h1 : is_positive_float vmin = false) (h2 : is_negative_float vmax = false)
    (h3 : is_negative_float amin = true) (h4 : is_positive_float amax = true)
    (h5 : is_positive_float j = true) :
    ∃ X : Float32, shape_pos_vel_accel pd vd ad p v a vmin vmax amin amax j dt true =
      shape_accel (constrain_value_line_float
        (constrain_value_line_float X amin amax (Int32.toUInt32 334) + ad) amin amax
          (Int32.toUInt32 341)) a j dt := by
  simp only [shape_pos_vel_accel, Id.run, h1, h2, h3, h4, h5, Bool.false_eq_true, ite_false,
    ite_true, id_pure_eq, Bool.or_false, Bool.not_true]
  split_ifs <;> exact ⟨_, rfl⟩

/-- The doubly clamped target is finite and within `[amin, amax]` whatever `X` is (NaN and
infinities included), when `ad` is a zero. -/
theorem tgt_mem {X ad amin amax : Float32} (hamin : amin.IsFinite) (hamax : amax.IsFinite)
    (had : ad.IsFinite) (had0 : ad.toReal = 0) (hle : amin.toReal ≤ amax.toReal)
    (hb1 : |amin.toReal| ≤ 2 ^ (100 : ℤ)) (hb2 : |amax.toReal| ≤ 2 ^ (100 : ℤ)) :
    (constrain_value_line_float (constrain_value_line_float X amin amax (Int32.toUInt32 334) + ad)
      amin amax (Int32.toUInt32 341)).IsFinite ∧
    amin.toReal ≤ (constrain_value_line_float (constrain_value_line_float X amin amax
      (Int32.toUInt32 334) + ad) amin amax (Int32.toUInt32 341)).toReal ∧
    (constrain_value_line_float (constrain_value_line_float X amin amax (Int32.toUInt32 334) + ad)
      amin amax (Int32.toUInt32 341)).toReal ≤ amax.toReal := by
  have hm : (2 : ℝ) ^ (100 : ℤ) ≤ maxFinite32 / 2 := by
    have := capF_le_max32; rw [Float32.maxFinite32_eq] at this ⊢
    have h1 : (2 : ℝ) ^ (101 : ℤ) ≤ 2 ^ (127 : ℤ) := zpow_le_zpow_right₀ one_le_two (by norm_num)
    have h2 : (2 : ℝ) ^ (-23 : ℤ) ≤ 1 / 2 := by norm_num
    have h3 : (2 : ℝ) ^ (101 : ℤ) = 2 * 2 ^ (100 : ℤ) := by
      rw [show (101 : ℤ) = 1 + 100 by norm_num, zpow_add₀ two_ne_zero]; norm_num
    nlinarith [zpow_pos (two_pos (α := ℝ)) (127 : ℤ)]
  obtain ⟨f1, l1, u1⟩ := Float32.cvl_between Float32.two32 (amt := X) hamin hamax
    (hb1.trans hm) (hb2.trans hm)
  rw [min_eq_left hle] at l1; rw [max_eq_right hle] at u1
  obtain ⟨f2, v2⟩ := Float32.add_zero_val f1 had had0
  have e1 : constrain_value_line_float X amin amax (Int32.toUInt32 334) =
      Float32.cvl X amin amax := rfl
  rw [e1]
  rw [constrain_inside _ f2 hamin hamax (by rw [v2]; exact l1) (by rw [v2]; exact u1)]
  exact ⟨f2, by rw [v2]; exact l1, by rw [v2]; exact u1⟩

/-- **The jerk-limited step keeps the acceleration bound** (exact facts of the clamps plus the
rounding of the final sum): from `|a| ≤ A + c` and a target `|T| ≤ A`, the new acceleration is
within `A + c` and moves by at most `J` (plus `10⁻⁵`), for `c ≥ 10⁻⁵`. -/
theorem shape_accel_bound {T a j dt : Float32} {Af c J : ℝ}
    (hj : is_positive_float j = true) (hd : is_positive_float dt = true)
    (hT : T.IsFinite) (hTb : |T.toReal| ≤ Af) (ha : a.IsFinite) (hab : |a.toReal| ≤ Af + c)
    (hlo : (-j * dt).IsFinite) (hhi : (j * dt).IsFinite)
    (hlo1 : -J ≤ (-j * dt).toReal) (hlo2 : (-j * dt).toReal ≤ 0)
    (hhi1 : 0 ≤ (j * dt).toReal) (hhi2 : (j * dt).toReal ≤ J)
    (hAf' : Af ≤ 64) (hJ : J ≤ 4) (hc : 1 / 10 ^ 5 ≤ c) (hc' : c ≤ 1) :
    (shape_accel T a j dt).IsFinite ∧ |(shape_accel T a j dt).toReal| ≤ Af + c ∧
      |(shape_accel T a j dt).toReal - a.toReal| ≤ J + 1 / 10 ^ 5 := by
  rw [shape_accel_eq hj hd]
  have hu : (2 : ℝ) ^ (-24 : ℤ) = 1 / 16777216 := by norm_num
  have hM := capF_le_max32
  simp only [capF] at hM
  have h100 : (200 : ℝ) ≤ 2 ^ (100 : ℤ) := by norm_num
  obtain ⟨hTl, hTu⟩ := abs_le.1 hTb
  obtain ⟨hal, hau⟩ := abs_le.1 hab
  have hx : |T.toReal - a.toReal| ≤ maxFinite32 := by
    rw [abs_le]; constructor <;> linarith
  obtain ⟨hd0f, hd0e⟩ := Float32.sub_err_all hT ha hx
  rw [hu] at hd0e
  have hlh : (-j * dt).toReal ≤ (j * dt).toReal := by linarith
  obtain ⟨hdf, hdv⟩ := constrain_spec (Int32.toUInt32 139) hd0f hlo hhi hlh
  have hsb := fun (f : Float32) (hf : f.IsFinite) => Float32.sub_bracket hT ha hx hf
  generalize T - a = d0 at hd0f hd0e hdf hdv hsb
  generalize constrain_value_line_float d0 (-j * dt) (j * dt) (Int32.toUInt32 139) = d at hdf hdv
  have hdlo : (-j * dt).toReal ≤ d.toReal := by rw [hdv]; exact le_max_left _ _
  have hdhi : d.toReal ≤ (j * dt).toReal := by rw [hdv]; exact max_le hlh (min_le_left _ _)
  have hs : |a.toReal + d.toReal| ≤ maxFinite32 := by rw [abs_le]; constructor <;> linarith
  obtain ⟨hsf, hse⟩ := Float32.add_err_all ha hdf hs
  rw [hu] at hse
  have hab' := fun (f : Float32) (hf : f.IsFinite) => Float32.add_bracket ha hdf hs hf
  have hse' := abs_le.1 hse
  have hd0e' := abs_le.1 hd0e
  have hsab : |a.toReal + d.toReal| ≤ Af + c + J := by rw [abs_le]; constructor <;> linarith
  have hsab' : 1 / 16777216 * |a.toReal + d.toReal| ≤ 1 / 16777216 * (Af + c + J) := by gcongr
  refine ⟨hsf, abs_le.2 ⟨?_, ?_⟩, ?_⟩
  · -- lower bound
    by_cases h1 : d0.toReal < (-j * dt).toReal
    · have hdl : d.toReal = (-j * dt).toReal := by
        rw [hdv]; exact max_eq_left ((min_le_right _ _).trans h1.le)
      have hxl : T.toReal - a.toReal < (-j * dt).toReal := by
        by_contra hc0; exact absurd ((hsb _ hlo).1 (not_lt.1 hc0)) (not_le.2 h1)
      have := (hab' _ hT).1 (by rw [hdl]; linarith)
      linarith
    · by_cases h2 : (j * dt).toReal < d0.toReal
      · have hdh : d.toReal = (j * dt).toReal := by
          rw [hdv, min_eq_left h2.le, max_eq_right hlh]
        have := (hab' _ ha).1 (by linarith)
        linarith
      · have hdd : d.toReal = d0.toReal := by
          rw [hdv, min_eq_right (not_lt.1 h2), max_eq_right (not_lt.1 h1)]
        by_cases h3 : 0 ≤ T.toReal - a.toReal
        · have h0 := (hsb _ Float32.isFinite_zero).1 (by rw [Float32.toReal_zero]; exact h3)
          rw [Float32.toReal_zero] at h0
          have := (hab' _ ha).1 (by linarith)
          linarith
        · have hxx : -(2 * J) ≤ T.toReal - a.toReal := by
            have : |T.toReal - a.toReal| = -(T.toReal - a.toReal) := abs_of_neg (not_le.1 h3)
            rw [this] at hd0e'
            nlinarith [hd0e'.1]
          have : |T.toReal - a.toReal| ≤ 2 * J := by
            rw [abs_of_neg (not_le.1 h3)]; linarith
          have : 1 / 16777216 * |T.toReal - a.toReal| ≤ 1 / 16777216 * (2 * J) := by gcongr
          linarith
  · -- upper bound
    by_cases h1 : (j * dt).toReal < d0.toReal
    · have hdh : d.toReal = (j * dt).toReal := by
        rw [hdv, min_eq_left h1.le, max_eq_right hlh]
      have hxl : (j * dt).toReal < T.toReal - a.toReal := by
        by_contra hc0; exact absurd ((hsb _ hhi).2 (not_lt.1 hc0)) (not_le.2 h1)
      have := (hab' _ hT).2 (by rw [hdh]; linarith)
      linarith
    · by_cases h2 : d0.toReal < (-j * dt).toReal
      · have hdl : d.toReal = (-j * dt).toReal := by
          rw [hdv]; exact max_eq_left ((min_le_right _ _).trans h2.le)
        have := (hab' _ ha).2 (by linarith)
        linarith
      · have hdd : d.toReal = d0.toReal := by
          rw [hdv, min_eq_right (not_lt.1 h1), max_eq_right (not_lt.1 h2)]
        by_cases h3 : T.toReal - a.toReal ≤ 0
        · have h0 := (hsb _ Float32.isFinite_zero).2 (by rw [Float32.toReal_zero]; exact h3)
          rw [Float32.toReal_zero] at h0
          have := (hab' _ ha).2 (by linarith)
          linarith
        · have : |T.toReal - a.toReal| ≤ 2 * J := by
            have h4 : |T.toReal - a.toReal| = T.toReal - a.toReal := abs_of_pos (not_le.1 h3)
            rw [h4] at hd0e' ⊢
            nlinarith [hd0e'.2]
          have : 1 / 16777216 * |T.toReal - a.toReal| ≤ 1 / 16777216 * (2 * J) := by gcongr
          linarith
  · rw [abs_le]; constructor <;> linarith

/-! ## The parameters -/

/-- The `float` time step `1/400` (`5368709 · 2⁻³¹`). -/
abbrev dtv : ℝ := 5368709 / 2147483648

/-- The `float` input time constant `0.05` (`13421773 · 2⁻²⁸`). -/
abbrev tcv : ℝ := 13421773 / 268435456

/-- Roll/pitch: the jerk limit `accel_max / input_tc` and the jerk step `± jerk · dt`, for an
`accel_max` within `10⁻⁵` of `10π` (`radians(1800)`), `input_tc = 0.05` and `dt = 1/400`. -/
theorem rp_consts (hL : LibmSpec) {am tc dt : Float32} (ham : am.IsFinite)
    (ham' : |am.toReal - 10 * Real.pi| ≤ 1 / 10 ^ 5) (htc : tc.IsFinite) (htc' : tc.toReal = tcv)
    (hdt : dt.IsFinite) (hdt' : dt.toReal = dtv) :
    A32 (am / tc) (am.toReal / tcv) (38 / 10 ^ 6) ∧
      A32 (am / tc * dt) (Real.pi / 2) (1 / 10 ^ 6) ∧
      A32 (-(am / tc) * dt) (-(Real.pi / 2)) (1 / 10 ^ 6) := by
  have _ := hL
  obtain ⟨p1, p2⟩ := pi_bounds
  obtain ⟨a1, a2⟩ := abs_le.1 ham'
  have hj := A32.div_c (A32.of_exact ham) (A32.of_exact htc) (Ra := 3142 / 100) (m := 1 / 20 - 1 / 10 ^ 8)
    (Q := 629) (by rw [abs_le]; constructor <;> linarith) (by norm_num)
    (by rw [htc']; norm_num) le_rfl
    (by rw [htc', abs_div, abs_of_pos (by norm_num : (0:ℝ) < tcv), div_le_iff₀ (by norm_num),
      abs_le]; constructor <;> norm_num [tcv] <;> linarith)
    (by norm_num [capF]) (e := 38 / 10 ^ 6) (by norm_num)
  rw [htc'] at hj
  have hdA : A32 dt dtv 0 := A32.of_val hdt hdt'
  have hb : |am.toReal / tcv| ≤ 629 := by
    rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < tcv), div_le_iff₀ (by norm_num), abs_le]
    constructor <;> norm_num [tcv] <;> linarith
  have hhi := A32.mul_c hj hdA hb (Rb := 1 / 400) (by norm_num [dtv])
    (by norm_num) le_rfl (by norm_num [capF]) (e := 2 / 10 ^ 7) (by norm_num)
  have hlo := A32.mul_c (A32.neg hj) hdA (Ra := 629) (by rw [abs_neg]; exact hb) (Rb := 1 / 400)
    (by norm_num [dtv]) (by norm_num) le_rfl (by norm_num [capF])
    (e := 2 / 10 ^ 7) (by norm_num)
  have hc : |am.toReal / tcv * dtv - Real.pi / 2| ≤ 8 / 10 ^ 7 := by
    rw [abs_le]; constructor <;> norm_num <;> linarith
  refine ⟨hj, (A32.recenter hhi hc).mono (by norm_num), (A32.recenter hlo (d := 8 / 10 ^ 7) ?_).mono (by norm_num)⟩
  rw [show -(am.toReal / tcv) * dtv - -(Real.pi / 2) = -(am.toReal / tcv * dtv - Real.pi / 2) by
    ring, abs_neg]
  exact hc

/-! ## (c) The acceleration invariant -/

/-- **(c), roll and pitch** (`max_ang_vel = 0`, `accel_max ≈ radians(1800)`, `input_tc = 0.05`,
`dt = 1/400`): for every input whatever its value (the error angle, the desired and the target
angular velocity need not even be finite), a finite target acceleration `α` with
`|α| ≤ accel_max + 10⁻⁵` is mapped to a finite `α'` with `|α'| ≤ accel_max + 10⁻⁵`, moving by at
most `π/2 + 2·10⁻⁵ = jerk·dt` (plus rounding). `accel_max` is the real value of the `float`. -/
theorem rp_accel_invariant (hL : LibmSpec) (e dv ω α vm am tc dt : Float32)
    (hvm : vm.IsFinite) (hvm0 : vm.toReal = 0)
    (ham : am.IsFinite) (ham' : |am.toReal - 10 * Real.pi| ≤ 1 / 10 ^ 5)
    (htc : tc.IsFinite) (htc' : tc.toReal = tcv) (hdt : dt.IsFinite) (hdt' : dt.toReal = dtv)
    (hα : α.IsFinite) (hαb : |α.toReal| ≤ am.toReal + 1 / 10 ^ 5) :
    (AC_AttitudeControl_Multi.attitude_command_model e dv ω α vm am tc dt).2.IsFinite ∧
      |(AC_AttitudeControl_Multi.attitude_command_model e dv ω α vm am tc dt).2.toReal| ≤
        am.toReal + 1 / 10 ^ 5 ∧
      |(AC_AttitudeControl_Multi.attitude_command_model e dv ω α vm am tc dt).2.toReal -
        α.toReal| ≤ Real.pi / 2 + 2 / 10 ^ 5 := by
  obtain ⟨p1, p2⟩ := pi_bounds
  obtain ⟨a1, a2⟩ := abs_le.1 ham'
  obtain ⟨hj, hhi, hlo⟩ := rp_consts hL ham ham' htc htc' hdt hdt'
  have hdtp : is_positive_float dt = true := isPos_true hdt (by rw [hdt']; norm_num)
  have hamp : is_positive_float am = true := isPos_true ham (by norm_num; linarith)
  have htcp : is_positive_float tc = true := isPos_true htc (by rw [htc']; norm_num)
  have hjp : is_positive_float (am / tc) = true := isPos_true hj.1 (by
    have := A32.lo hj; norm_num at this ⊢; linarith)
  have hnam : (-am).IsFinite := (Float32.isFinite_neg am).2 ham
  have h1 : is_positive_float (-vm) = false :=
    isPos_false ((Float32.isFinite_neg vm).2 hvm) (by rw [Float32.toReal_neg, hvm0]; norm_num)
  have h2 : is_negative_float vm = false := isNeg_false hL hvm (by rw [hvm0]; norm_num)
  have h3 : is_negative_float (-am) = true := isNeg_true hL hnam (by
    rw [Float32.toReal_neg]; norm_num; linarith)
  simp only [AC_AttitudeControl_Multi.attitude_command_model, Id.run, hdtp, hamp, htcp,
    Bool.not_true, Bool.false_eq_true, ite_false, id_pure_eq, shape_angle_vel_accel]
  obtain ⟨X, hX⟩ := spva_any (pd := Float32.toFloat (Float.toFloat32 (0.0 : Float) +
      wrap_PI_float (e - Float.toFloat32 (0.0 : Float))))
    (p := Float32.toFloat (Float.toFloat32 (0.0 : Float))) (vd := dv) (ad := Float.toFloat32 0.0)
    (v := ω) (a := α) (dt := dt) h1 h2 h3 hamp hjp
  rw [hX]
  obtain ⟨hzf, hz0⟩ := zf hL
  obtain ⟨tf, tl, tu⟩ := tgt_mem (X := X) hnam ham hzf hz0 (by rw [Float32.toReal_neg]; linarith)
    (by rw [Float32.toReal_neg, abs_neg, abs_le]; constructor <;> norm_num <;> linarith)
    (by rw [abs_le]; constructor <;> norm_num <;> linarith)
  rw [Float32.toReal_neg] at tl
  have hb := shape_accel_bound (Af := am.toReal) (c := 1 / 10 ^ 5) (J := Real.pi / 2 + 1 / 10 ^ 6)
    hjp hdtp tf (abs_le.2 ⟨tl, tu⟩) hα hαb hlo.1 hhi.1
    (by have := A32.lo hlo; linarith) (by have := A32.hi hlo; linarith)
    (by have := A32.lo hhi; linarith) (by have := A32.hi hhi; linarith)
    (by linarith) (by linarith) (by norm_num) (by norm_num)
  exact ⟨hb.1, hb.2.1, by linarith [hb.2.2]⟩

/-- Yaw: `input_tc = _rate_y_tc = 0` is replaced by `dt · 10`; the jerk limit
`accel_max / (dt · 10)` and the jerk step `± jerk · dt ≈ accel_max / 10`, for an `accel_max`
within `10⁻⁵` of `3π/2` (`radians(270)`). -/
theorem yaw_consts (hL : LibmSpec) {am dt : Float32} (ham : am.IsFinite)
    (ham' : |am.toReal - 3 * Real.pi / 2| ≤ 1 / 10 ^ 5) (hdt : dt.IsFinite) (hdt' : dt.toReal = dtv) :
    A32 (dt * Float.toFloat32 (10.0 : Float)) (dtv * 10) (2 / 10 ^ 9) ∧
      A32 (am / (dt * Float.toFloat32 (10.0 : Float))) (am.toReal / (dtv * 10)) (3 / 10 ^ 5) ∧
      A32 (am / (dt * Float.toFloat32 (10.0 : Float)) * dt) (3 * Real.pi / 20) (2 / 10 ^ 6) ∧
      A32 (-(am / (dt * Float.toFloat32 (10.0 : Float))) * dt) (-(3 * Real.pi / 20)) (2 / 10 ^ 6) := by
  obtain ⟨p1, p2⟩ := pi_bounds
  obtain ⟨a1, a2⟩ := abs_le.1 ham'
  obtain ⟨tf, tv⟩ := tenf hL
  have hdA : A32 dt dtv 0 := A32.of_val hdt hdt'
  have htc := A32.mul_c hdA (A32.of_val tf tv) (Ra := 1 / 400) (Rb := 10) (by norm_num [dtv])
    (by norm_num) le_rfl le_rfl (by norm_num [capF]) (e := 2 / 10 ^ 9) (by norm_num)
  have hj := A32.div_c (A32.of_exact ham) htc (Ra := 4713 / 1000) (m := 1 / 40 - 1 / 10 ^ 8)
    (Q := 1886 / 10) (by rw [abs_le]; constructor <;> linarith) (by norm_num)
    (by norm_num [dtv]) (by norm_num)
    (by rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < dtv * 10), div_le_iff₀ (by norm_num),
      abs_le]; constructor <;> norm_num [dtv] <;> linarith)
    (by norm_num [capF]) (e := 3 / 10 ^ 5) (by norm_num)
  have hb : |am.toReal / (dtv * 10)| ≤ 1886 / 10 := by
    rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < dtv * 10), div_le_iff₀ (by norm_num), abs_le]
    constructor <;> norm_num [dtv] <;> linarith
  have hhi := A32.mul_c hj hdA (Ra := 1886 / 10) hb (Rb := 1 / 400) (by norm_num [dtv])
    (by norm_num) le_rfl (by norm_num [capF]) (e := 2 / 10 ^ 7) (by norm_num)
  have hlo := A32.mul_c (A32.neg hj) hdA (Ra := 1886 / 10) (by rw [abs_neg]; exact hb)
    (Rb := 1 / 400) (by norm_num [dtv]) (by norm_num) le_rfl (by norm_num [capF])
    (e := 2 / 10 ^ 7) (by norm_num)
  have hc : |am.toReal / (dtv * 10) * dtv - 3 * Real.pi / 20| ≤ 1 / 10 ^ 6 := by
    rw [show am.toReal / (dtv * 10) * dtv = am.toReal / 10 by field_simp]
    rw [abs_le]; constructor <;> linarith
  refine ⟨htc, hj, (A32.recenter hhi hc).mono (by norm_num),
    (A32.recenter hlo (d := 1 / 10 ^ 6) ?_).mono (by norm_num)⟩
  rw [show -(am.toReal / (dtv * 10)) * dtv - -(3 * Real.pi / 20) =
    -(am.toReal / (dtv * 10) * dtv - 3 * Real.pi / 20) by ring, abs_neg]
  exact hc

/-- **(c), yaw** (`max_ang_vel = slew ≈ radians(60)`, `accel_max ≈ radians(270)`,
`input_tc = 0 → dt·10`, `dt = 1/400`): the same invariant, with the jerk step
`3π/20 = accel_max/10`. -/
theorem yaw_accel_invariant (hL : LibmSpec) (e dv ω α vm am tc dt : Float32)
    (hvm : vm.IsFinite) (hvm' : |vm.toReal - Real.pi / 3| ≤ 1 / 10 ^ 5)
    (ham : am.IsFinite) (ham' : |am.toReal - 3 * Real.pi / 2| ≤ 1 / 10 ^ 5)
    (htc : tc.IsFinite) (htc0 : tc.toReal = 0) (hdt : dt.IsFinite) (hdt' : dt.toReal = dtv)
    (hα : α.IsFinite) (hαb : |α.toReal| ≤ am.toReal + 1 / 10 ^ 5) :
    (AC_AttitudeControl_Multi.attitude_command_model e dv ω α vm am tc dt).2.IsFinite ∧
      |(AC_AttitudeControl_Multi.attitude_command_model e dv ω α vm am tc dt).2.toReal| ≤
        am.toReal + 1 / 10 ^ 5 ∧
      |(AC_AttitudeControl_Multi.attitude_command_model e dv ω α vm am tc dt).2.toReal -
        α.toReal| ≤ 3 * Real.pi / 20 + 2 / 10 ^ 5 := by
  obtain ⟨p1, p2⟩ := pi_bounds
  obtain ⟨a1, a2⟩ := abs_le.1 ham'
  obtain ⟨v1, v2⟩ := abs_le.1 hvm'
  obtain ⟨_, hj, hhi, hlo⟩ := yaw_consts hL ham ham' hdt hdt'
  have hdtp : is_positive_float dt = true := isPos_true hdt (by rw [hdt']; norm_num)
  have hamp : is_positive_float am = true := isPos_true ham (by norm_num; linarith)
  have htcp : is_positive_float tc = false := isPos_false htc (by rw [htc0]; norm_num)
  have hjp : is_positive_float (am / (dt * Float.toFloat32 (10.0 : Float))) = true :=
    isPos_true hj.1 (by have := A32.lo hj; norm_num [dtv] at this ⊢; linarith)
  have hnam : (-am).IsFinite := (Float32.isFinite_neg am).2 ham
  have h1 : is_positive_float (-vm) = false :=
    isPos_false ((Float32.isFinite_neg vm).2 hvm) (by rw [Float32.toReal_neg]; norm_num; linarith)
  have h2 : is_negative_float vm = false := isNeg_false hL hvm (by norm_num; linarith)
  have h3 : is_negative_float (-am) = true := isNeg_true hL hnam (by
    rw [Float32.toReal_neg]; norm_num; linarith)
  simp only [AC_AttitudeControl_Multi.attitude_command_model, Id.run, hdtp, hamp, htcp,
    Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_false, ite_true, id_pure_eq,
    shape_angle_vel_accel]
  obtain ⟨X, hX⟩ := spva_any (pd := Float32.toFloat (Float.toFloat32 (0.0 : Float) +
      wrap_PI_float (e - Float.toFloat32 (0.0 : Float))))
    (p := Float32.toFloat (Float.toFloat32 (0.0 : Float))) (vd := dv) (ad := Float.toFloat32 0.0)
    (v := ω) (a := α) (dt := dt) h1 h2 h3 hamp hjp
  rw [hX]
  obtain ⟨hzf, hz0⟩ := zf hL
  obtain ⟨tf, tl, tu⟩ := tgt_mem (X := X) hnam ham hzf hz0 (by rw [Float32.toReal_neg]; linarith)
    (by rw [Float32.toReal_neg, abs_neg, abs_le]; constructor <;> norm_num <;> linarith)
    (by rw [abs_le]; constructor <;> norm_num <;> linarith)
  rw [Float32.toReal_neg] at tl
  have hb := shape_accel_bound (Af := am.toReal) (c := 1 / 10 ^ 5)
    (J := 3 * Real.pi / 20 + 2 / 10 ^ 6)
    hjp hdtp tf (abs_le.2 ⟨tl, tu⟩) hα hαb hlo.1 hhi.1
    (by have := A32.lo hlo; linarith) (by have := A32.hi hlo; linarith)
    (by have := A32.lo hhi; linarith) (by have := A32.hi hhi; linarith)
    (by linarith) (by linarith) (by norm_num) (by norm_num)
  exact ⟨hb.1, hb.2.1, by linarith [hb.2.2]⟩

/-! ## Pieces of the law -/

/-- A nonzero `float` is at least the smallest subnormal `2⁻¹⁴⁹` in magnitude. -/
theorem f32_abs_ge_min {x : Float32} (hx : x.toReal ≠ 0) : 2 ^ (-149 : ℤ) ≤ |x.toReal| := by
  have hc := Float32.Model.unpack_canonical32 x.toModel
  unfold Float32.toReal at hx ⊢
  cases h : x.toModel.unpack with
  | finite s m e hm =>
    rw [h] at hc hx
    rw [UnpackedFloat.toReal]
    have he : -149 ≤ e := hc.1
    have hm1 : (1 : ℝ) ≤ m := by exact_mod_cast hm
    have hs : |((s.apply (m : ℤ) : ℤ) : ℝ)| = m := by
      cases s <;> simp [Sign.apply]
    rw [abs_mul, hs, abs_of_pos (zpow_pos two_pos e)]
    calc (2 : ℝ) ^ (-149 : ℤ) ≤ 2 ^ e := zpow_le_zpow_right₀ one_le_two he
      _ = 1 * 2 ^ e := (one_mul _).symm
      _ ≤ m * 2 ^ e := mul_le_mul_of_nonneg_right hm1 (zpow_pos two_pos e).le
  | _ => rw [h] at hx; exact absurd rfl hx

/-- The final clamp of `sqrt_controller` (`±|error|/dt`) is inactive on the linear branch
`error · p` for `0 ≤ p ≤ 64` and `dt ≤ 1/200`. -/
theorem sqrtc_clamp_lin {pe k dt : Float32} (line : UInt32) (hpe : pe.IsFinite) (hpe1 : |pe.toReal| ≤ 1)
    (hk : k.IsFinite) (hk0 : 0 ≤ k.toReal) (hk1 : k.toReal ≤ 64) (hdt : dt.IsFinite)
    (hd0 : 1 / 1000 ≤ dt.toReal) (hd1 : dt.toReal ≤ 1 / 200) :
    constrain_value_line_float (pe * k) (-(Float32.abs pe) / dt) (Float32.abs pe / dt) line =
      pe * k := by
  have hab := (Float32.isFinite_abs pe).2 hpe
  have hnab := (Float32.isFinite_neg _).2 hab
  have habv : (Float32.abs pe).toReal = |pe.toReal| := Float32.toReal_abs pe
  have hM := capF_le_max32
  simp only [capF] at hM
  have h1000 : (2000 : ℝ) ≤ 2 ^ (100 : ℤ) := by norm_num
  have hdt0 : dt.toReal ≠ 0 := by linarith
  have hq1 : |(Float32.abs pe).toReal / dt.toReal| ≤ maxFinite32 := by
    rw [habv, abs_div, abs_abs, abs_of_pos (show (0:ℝ) < dt.toReal by linarith),
      div_le_iff₀ (show (0:ℝ) < dt.toReal by linarith)]
    nlinarith [abs_nonneg pe.toReal]
  have hq2 : |(-(Float32.abs pe)).toReal / dt.toReal| ≤ maxFinite32 := by
    rw [Float32.toReal_neg, neg_div, abs_neg]; exact hq1
  have hp : |pe.toReal * k.toReal| ≤ maxFinite32 := by
    rw [abs_mul, abs_of_nonneg hk0]; nlinarith [abs_nonneg pe.toReal]
  obtain ⟨hf1, he1⟩ := Float32.div_err_all hab hdt hdt0 hq1
  obtain ⟨hf2, he2⟩ := Float32.div_err_all hnab hdt hdt0 hq2
  obtain ⟨hf3, he3⟩ := Float32.mul_err_all hpe hk hp
  rcases eq_or_ne pe.toReal 0 with h0 | h0
  · have hm := (Float32.mul_exact hpe hk hpe (by rw [h0, zero_mul])).2
    have hz1 : (Float32.abs pe / dt).toReal = 0 := by
      have b := Float32.div_bracket hab hdt hdt0 hq1 hpe
      rw [habv, h0, abs_zero, zero_div] at b
      exact le_antisymm (b.2 le_rfl) (b.1 le_rfl)
    have hz2 : (-(Float32.abs pe) / dt).toReal = 0 := by
      have b := Float32.div_bracket hnab hdt hdt0 hq2 hpe
      rw [Float32.toReal_neg, habv, h0, abs_zero, neg_zero, zero_div] at b
      exact le_antisymm (b.2 le_rfl) (b.1 le_rfl)
    exact constrain_inside line hf3 hf2 hf1 (by rw [hz2, hm, h0]) (by rw [hz1, hm, h0])
  · have hmin := f32_abs_ge_min h0
    have h150 : (2 : ℝ) ^ (-150 : ℤ) = 2 ^ (-149 : ℤ) / 2 := by
      rw [show (-150 : ℤ) = -149 + -1 by norm_num, zpow_add₀ two_ne_zero]; norm_num
    have hu : (2 : ℝ) ^ (-24 : ℤ) = 1 / 16777216 := by norm_num
    rw [hu, h150] at he1 he2 he3
    rw [habv] at he1
    rw [Float32.toReal_neg, habv] at he2
    have hP : 0 < |pe.toReal| := abs_pos.2 h0
    have hx : |pe.toReal| / dt.toReal ≥ 200 * |pe.toReal| := by
      rw [ge_iff_le, le_div_iff₀ (by linarith)]; nlinarith
    rw [abs_div, abs_abs, abs_of_pos (by linarith : (0:ℝ) < dt.toReal)] at he1
    rw [neg_div, abs_neg, abs_div, abs_abs, abs_of_pos (by linarith : (0:ℝ) < dt.toReal)] at he2
    have hpk : |pe.toReal * k.toReal| ≤ 64 * |pe.toReal| := by
      rw [abs_mul, abs_of_nonneg hk0]; nlinarith
    obtain ⟨e1, e1'⟩ := abs_le.1 he1
    obtain ⟨e2, e2'⟩ := abs_le.1 he2
    obtain ⟨e3, e3'⟩ := abs_le.1 he3
    obtain ⟨e4, e4'⟩ := abs_le.1 hpk
    have hd : |pe.toReal| / dt.toReal ≤ 1000 * |pe.toReal| := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    have s1 : (-(Float32.abs pe) / dt).toReal ≤
        -(|pe.toReal| / dt.toReal) * (1 - 1 / 16777216) + 2 ^ (-149 : ℤ) / 2 := by linarith
    have s1' : (Float32.abs pe / dt).toReal ≥
        (|pe.toReal| / dt.toReal) * (1 - 1 / 16777216) - 2 ^ (-149 : ℤ) / 2 := by linarith
    have s2 : (|pe.toReal| / dt.toReal) * (1 - 1 / 16777216) ≥ (200 * |pe.toReal|) * (1 - 1 / 16777216) := by
      nlinarith
    have s3 : (pe * k).toReal ≥ -(64 * |pe.toReal|) - 1 / 16777216 * (64 * |pe.toReal|) - 2 ^ (-149 : ℤ) / 2 := by
      nlinarith
    have s3' : (pe * k).toReal ≤ 64 * |pe.toReal| + 1 / 16777216 * (64 * |pe.toReal|) + 2 ^ (-149 : ℤ) / 2 := by
      nlinarith
    have hm0 : (0:ℝ) < 2 ^ (-149 : ℤ) := zpow_pos two_pos _
    generalize (2:ℝ) ^ (-149 : ℤ) = m at *
    generalize |pe.toReal| = A at *
    generalize |pe.toReal| / dt.toReal = x at *
    refine constrain_inside line hf3 hf2 hf1 ?_ ?_
    · linarith
    · linarith

/-- The error angle after `shape_angle_vel_accel`'s wrap and the `double` round trip:
`(float)((double)(0 + wrap_PI(e - 0)) - (double) 0)`, within `1.4·10⁻⁶` of `e` for `|e| ≤ 3`
(exact for `e ≥ 0`). -/
theorem posErr_near (hL : LibmSpec) {e : Float32} (he : e.IsFinite) (he3 : |e.toReal| ≤ 3) :
    A32 (Float.toFloat32 (Float32.toFloat (Float.toFloat32 (0.0 : Float) +
        wrap_PI_float (e - Float.toFloat32 (0.0 : Float))) -
        Float32.toFloat (Float.toFloat32 (0.0 : Float)))) e.toReal (14 / 10 ^ 7) ∧
    (0 ≤ e.toReal → (Float.toFloat32 (Float32.toFloat (Float.toFloat32 (0.0 : Float) +
        wrap_PI_float (e - Float.toFloat32 (0.0 : Float))) -
        Float32.toFloat (Float.toFloat32 (0.0 : Float)))).toReal = e.toReal) := by
  obtain ⟨hzf, hz0⟩ := zf hL
  obtain ⟨hdf, hdv⟩ := Float32.sub_zero_val he hzf hz0
  obtain ⟨hw, hw0⟩ := wrapPI_near hL hdf (by rw [hdv]; exact he3)
  rw [hdv] at hw hw0
  obtain ⟨hsf, hsv⟩ := Float32.add_exact hzf hw.1 hw.1 (by rw [hz0, zero_add])
  generalize wrap_PI_float (e - Float.toFloat32 (0.0 : Float)) = w at hw hw0 hsf hsv ⊢
  generalize Float.toFloat32 (0.0 : Float) + w = s at hsf hsv ⊢
  obtain ⟨f1, v1⟩ := hL.f32ToF64 s hsf
  obtain ⟨f2, v2⟩ := hL.f32ToF64 _ hzf
  have hm : |(Float32.toFloat s).toReal - (Float32.toFloat (Float.toFloat32 (0.0 : Float))).toReal| ≤
      maxFinite := by
    rw [v1, v2, hz0, sub_zero, hsv]
    have := Float32.abs_toReal_le_maxFinite w
    have : maxFinite32 ≤ maxFinite := by
      rw [Float32.maxFinite32_eq]; unfold maxFinite
      have h1 : (2 : ℝ) ^ (127 : ℤ) ≤ 2 ^ (971 : ℤ) := zpow_le_zpow_right₀ one_le_two (by norm_num)
      have h3 : (2 : ℝ) - 2 ^ (-23 : ℤ) ≤ 2 ^ 53 - 1 := by norm_num
      have h4 : (0 : ℝ) ≤ 2 - 2 ^ (-23 : ℤ) := by norm_num
      exact mul_le_mul h3 h1 (by positivity) (by norm_num)
    linarith
  have hb := Float.sub_bracket f1 f2 hm f1
  rw [v2, hz0, sub_zero] at hb
  have hdv' : (Float32.toFloat s - Float32.toFloat (Float.toFloat32 (0.0 : Float))).toReal =
      s.toReal := by
    rw [← v1]; exact le_antisymm (hb.2 le_rfl) (hb.1 le_rfl)
  obtain ⟨f3, v3⟩ := hL.f64ToF32_exact _ s (Float.sub_err_all f1 f2 hm).1 hsf hdv'.symm
  rw [hdv', hsv] at v3
  exact ⟨⟨f3, by rw [v3]; exact hw.2⟩, fun h => by rw [v3]; exact hw0 h⟩

/-- The jerk-limited step of approximations: the real law `a + clamp(T - a, ±J)`. -/
theorem shape_accel_law {T a j dt : Float32} {tr J εT εJ : ℝ}
    (hj : is_positive_float j = true) (hd : is_positive_float dt = true)
    (hT : A32 T tr εT) (ha : a.IsFinite) (hab : |a.toReal| ≤ 32) (htr : |tr| ≤ 32)
    (hlo : A32 (-j * dt) (-J) εJ) (hhi : A32 (j * dt) J εJ) (hlh : (-j * dt).toReal ≤ (j * dt).toReal)
    (hJ0 : 0 ≤ J) (hJ : J ≤ 2) (hεT : εT ≤ 1 / 10) (hεJ : εJ ≤ 1 / 100) :
    A32 (shape_accel T a j dt) (a.toReal + clampR (-J) J (tr - a.toReal))
      (εT + 2 * εJ + 1 / 10 ^ 5) := by
  rw [shape_accel_eq hj hd]
  have hεT0 := A32.e_nonneg hT
  have hεJ0 := A32.e_nonneg hlo
  have h1 : |tr - a.toReal| ≤ 64 := by have := abs_sub tr a.toReal; linarith
  have hcl := abs_clampR_le (x := tr - a.toReal) hJ0
  have h2 : |a.toReal + clampR (-J) J (tr - a.toReal)| ≤ 34 := by
    have := abs_add_le a.toReal (clampR (-J) J (tr - a.toReal)); linarith
  have hη := η32_small
  have hη0 := η32_pos
  have hd0 := A32.sub hT (A32.of_exact ha) (by norm_num; linarith)
  have hc := A32.cvl (Int32.toUInt32 139) hd0 hlo hhi hlh
  have hs := A32.add (A32.of_exact ha) hc (by
    simp only [u32]; norm_num
    have : 1 / 16777216 * (|tr - a.toReal| + εT) ≤ 1 / 16777216 * (64 + 1 / 10) := by gcongr
    linarith)
  refine (hs.congr rfl).mono ?_
  simp only [u32]
  norm_num
  have : 1 / 16777216 * (|tr - a.toReal| + εT) ≤ 1 / 16777216 * (64 + 1 / 10) := by gcongr
  have : 1 / 16777216 * (|a.toReal + clampR (-J) J (tr - a.toReal)| +
      (εT + 1 / 16777216 * (|tr - a.toReal| + εT) + η32 + εJ + εJ)) ≤ 1 / 16777216 * (35) := by
    gcongr; linarith
  linarith

/-! ## `sqrt_controller` and `sqrt_controller_accel` branches -/

theorem sc_eq_lin {pe k al dt : Float32} (h1 : is_negative_float al = false)
    (h2 : is_zero_float al = false) (h3 : is_zero_float k = false)
    (h4 : is_positive_float dt = true) (h5 : ¬ pe > al / sq_float k)
    (h6 : ¬ pe < -(al / sq_float k)) :
    sqrt_controller_float4 pe k al dt = constrain_value_line_float (pe * k)
      (-(Float32.abs pe) / dt) (Float32.abs pe / dt) (Int32.toUInt32 606) := by
  simp only [sqrt_controller_float4, Id.run, id_pure_eq, h1, h2, h3, h4, Bool.or_false,
    Bool.false_eq_true, ite_false, ite_true]
  rw [ite_eq_right h5, ite_eq_right h6]

theorem sc_eq_pos {pe k al dt : Float32} (h1 : is_negative_float al = false)
    (h2 : is_zero_float al = false) (h3 : is_zero_float k = false)
    (h4 : is_positive_float dt = true) (h5 : pe > al / sq_float k) :
    sqrt_controller_float4 pe k al dt = constrain_value_line_float
      (safe_sqrt_float (Float.toFloat32 2.0 * al * (pe - al / sq_float k / Float.toFloat32 2.0)))
      (-(Float32.abs pe) / dt) (Float32.abs pe / dt) (Int32.toUInt32 606) := by
  simp only [sqrt_controller_float4, Id.run, id_pure_eq, h1, h2, h3, h4, Bool.or_false,
    Bool.false_eq_true, ite_false, ite_true]
  rw [ite_eq_left h5]

theorem sc_eq_neg {pe k al dt : Float32} (h1 : is_negative_float al = false)
    (h2 : is_zero_float al = false) (h3 : is_zero_float k = false)
    (h4 : is_positive_float dt = true) (h5 : ¬ pe > al / sq_float k)
    (h6 : pe < -(al / sq_float k)) :
    sqrt_controller_float4 pe k al dt = constrain_value_line_float
      (-safe_sqrt_float (Float.toFloat32 2.0 * al * (-pe - al / sq_float k / Float.toFloat32 2.0)))
      (-(Float32.abs pe) / dt) (Float32.abs pe / dt) (Int32.toUInt32 606) := by
  simp only [sqrt_controller_float4, Id.run, id_pure_eq, h1, h2, h3, h4, Bool.or_false,
    Bool.false_eq_true, ite_false, ite_true]
  rw [ite_eq_right h5, ite_eq_left h6]

theorem sca_eq_zero {pe V vc k al : Float32} (h : is_positive_float (V * vc) = false) :
    sqrt_controller_accel pe V vc k al = Float.toFloat32 0.0 := by
  simp only [sqrt_controller_accel, Id.run, id_pure_eq, h, Bool.not_false, ite_true]

theorem sca_eq_lin {pe V vc k al : Float32} (h : is_positive_float (V * vc) = true)
    (hal : is_positive_float al = true) (hk : is_positive_float k = true)
    (hle : Float32.abs pe ≤ al / sq_float k) :
    sqrt_controller_accel pe V vc k al = -k * vc := by
  simp only [sqrt_controller_accel, Id.run, id_pure_eq, h, hal, hk, Bool.not_true,
    Bool.false_eq_true, ite_false]
  rw [ite_eq_left hle]

theorem sca_eq_sqrt {pe V vc k al : Float32} (h : is_positive_float (V * vc) = true)
    (hal : is_positive_float al = true) (hk : is_positive_float k = true)
    (hle : ¬ Float32.abs pe ≤ al / sq_float k) (hz : is_zero_float V = false) :
    sqrt_controller_accel pe V vc k al = -(al / Float32.abs V) * vc := by
  simp only [sqrt_controller_accel, Id.run, id_pure_eq, h, hal, hk, hz, Bool.not_true,
    Bool.false_eq_true, ite_false]
  rw [ite_eq_right hle]

/-! ## Roll/pitch: the gain `k_v = jerk / accel_lim` and the linear distance -/

/-- `k_v = (accel_max / input_tc) / accel_lim ≈ 1/input_tc ≈ 20` and the linear distance
`accel_lim / k_v² ≈ accel_max / 400 ≈ π/40`. -/
theorem rp_gain {am j al : Float32} (ham : am.IsFinite)
    (ham' : |am.toReal - 10 * Real.pi| ≤ 1 / 10 ^ 5) (hj : A32 j (am.toReal / tcv) (38 / 10 ^ 6))
    (hal : al.IsFinite) (hal' : al.toReal = am.toReal) :
    A32 (j / al) 20 (3 / 10 ^ 6) ∧ A32 (sq_float (j / al)) 400 (15 / 10 ^ 5) ∧
      A32 (al / sq_float (j / al)) (Real.pi / 40) (1 / 10 ^ 7) := by
  have _ := ham
  obtain ⟨p1, p2⟩ := pi_bounds
  obtain ⟨a1, a2⟩ := abs_le.1 ham'
  have hA : A32 al am.toReal 0 := A32.of_val hal hal'
  have ha0 : am.toReal ≠ 0 := by intro h; rw [h] at a1; linarith
  have hq : am.toReal / tcv / am.toReal = 1 / tcv := by field_simp
  have hk0 := A32.div_c hj hA (Ra := 629) (m := 3141 / 100) (Q := 2001 / 100)
    (by rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < tcv), div_le_iff₀ (by norm_num), abs_le]
        constructor <;> norm_num [tcv] <;> linarith)
    (by norm_num) (by rw [abs_of_pos (by linarith)]; linarith) le_rfl
    (by rw [hq]; norm_num [tcv]) (by norm_num [capF]) (e := 25 / 10 ^ 7) (by norm_num)
  rw [hq] at hk0
  have hk : A32 (j / al) 20 (3 / 10 ^ 6) :=
    (A32.recenter hk0 (d := 3 / 10 ^ 7) (by norm_num [tcv])).mono (by norm_num)
  have hsq0 := A32.mul_c hk hk (Ra := 20) (Rb := 20) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [capF]) (e := 15 / 10 ^ 5) (by norm_num)
  have hsq : A32 (sq_float (j / al)) 400 (15 / 10 ^ 5) := by
    have e : sq_float (j / al) = j / al * (j / al) := rfl
    rw [e]; exact hsq0.congr (by norm_num)
  have hld0 := A32.div_c hA hsq (Ra := 3142 / 100) (m := 39999 / 100) (Q := 786 / 10000)
    (by rw [abs_le]; constructor <;> linarith) (by norm_num) (by norm_num) (by norm_num)
    (by rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 400), div_le_iff₀ (by norm_num), abs_le]
        constructor <;> linarith)
    (by norm_num [capF]) (e := 4 / 10 ^ 8) (by norm_num)
  refine ⟨hk, hsq, (A32.recenter hld0 (d := 3 / 10 ^ 8) ?_).mono (by norm_num)⟩
  rw [show am.toReal / 400 - Real.pi / 40 = (am.toReal - 10 * Real.pi) / 400 by ring, abs_div,
    abs_of_pos (by norm_num : (0:ℝ) < 400), div_le_iff₀ (by norm_num)]
  linarith

theorem clampR_idem {l h x : ℝ} (hlh : l ≤ h) : clampR l h (clampR l h x) = clampR l h x :=
  clampR_of_mem le_clampR (clampR_le hlh)

/-- `0` or `1` for the Boolean of the `sqrt_controller_accel` test. -/
def sgn01 (σ : Bool) : ℝ := if σ then 1 else 0

theorem sgn01_nonneg (σ : Bool) : 0 ≤ sgn01 σ := by cases σ <;> simp [sgn01]
theorem sgn01_le (σ : Bool) : sgn01 σ ≤ 1 := by cases σ <;> simp [sgn01]

/-- The accuracy-carrying form of `(-am, am)` as clamp bounds. -/
theorem am_bounds {am : Float32} {A : ℝ} (ham : am.IsFinite) (ham' : |am.toReal - A| ≤ 1 / 10 ^ 5) :
    A32 (-am) (-A) (1 / 10 ^ 5) ∧ A32 am A (1 / 10 ^ 5) := ⟨A32.neg ⟨ham, ham'⟩, ⟨ham, ham'⟩⟩

/-- **The roll/pitch acceleration target, linear zone** (`|e| ≤ 0.0785 < π/40`, `|ω| ≤ 10`,
`desired_ang_vel = 0`): `clamp(20·(20 e − (1 + σ) ω), ±10π)` within `9·10⁻⁴`, where `σ` is the
Boolean of the test `is_positive(vel_corr_cmd · (ω − desired))` of `sqrt_controller_accel`, which
agrees with the real product `20 e ω ≥ 2⁻²³` up to `3.1·10⁻⁴`. -/
theorem tgtRoll_lin (hL : LibmSpec) {pe dv ad ω am j al dt : Float32} {er : ℝ}
    (hpe : A32 pe er (14 / 10 ^ 7)) (her : |er| ≤ 785 / 10000)
    (hdv : dv.IsFinite) (hdv0 : dv.toReal = 0) (had : ad.IsFinite) (had0 : ad.toReal = 0)
    (hω : ω.IsFinite) (hωb : |ω.toReal| ≤ 10)
    (ham : am.IsFinite) (ham' : |am.toReal - 10 * Real.pi| ≤ 1 / 10 ^ 5)
    (hj : A32 j (am.toReal / tcv) (38 / 10 ^ 6)) (hal : al.IsFinite) (hal' : al.toReal = am.toReal)
    (hdt : dt.IsFinite) (hdt' : dt.toReal = dtv) :
    ∃ σ : Bool, (σ = true → 2 ^ (-23 : ℤ) - 31 / 10 ^ 5 ≤ 20 * er * ω.toReal) ∧
      (σ = false → 20 * er * ω.toReal < 2 ^ (-23 : ℤ) + 31 / 10 ^ 5) ∧
      A32 (tgtRoll pe dv ad ω (-am) am j al dt)
        (clampR (-(10 * Real.pi)) (10 * Real.pi) (20 * (20 * er - (1 + sgn01 σ) * ω.toReal)))
        (9 / 10 ^ 4) := by
  obtain ⟨p1, p2⟩ := pi_bounds
  obtain ⟨a1, a2⟩ := abs_le.1 ham'
  obtain ⟨r1, r2⟩ := abs_le.1 her
  obtain ⟨w1, w2⟩ := abs_le.1 hωb
  obtain ⟨hk, hsq, hld⟩ := rp_gain ham ham' hj hal hal'
  have hpl := A32.lo hpe
  have hph := A32.hi hpe
  have hkl := A32.lo hk
  have hkh := A32.hi hk
  have hll := A32.lo hld
  have hlh := A32.hi hld
  have b1 : is_negative_float al = false := isNeg_false hL hal (by rw [hal']; norm_num; linarith)
  have b2 : is_zero_float al = false :=
    isZero_false hal (by rw [hal', abs_of_pos (by linarith)]; norm_num; linarith)
  have b3 : is_zero_float (j / al) = false :=
    isZero_false hk.1 (by rw [abs_of_pos (by linarith)]; norm_num; linarith)
  have b4 : is_positive_float dt = true := isPos_true hdt (by rw [hdt']; norm_num)
  have b5 : is_positive_float al = true := isPos_true hal (by rw [hal']; norm_num; linarith)
  have b6 : is_positive_float (j / al) = true := isPos_true hk.1 (by norm_num; linarith)
  have c5 : ¬ pe > al / sq_float (j / al) := by
    rw [gt_iff_lt, Float32.lt_iff_toReal_lt hld.1 hpe.1]; linarith
  have c6 : ¬ pe < -(al / sq_float (j / al)) := by
    rw [Float32.lt_iff_toReal_lt hpe.1 ((Float32.isFinite_neg _).2 hld.1), Float32.toReal_neg]
    linarith
  have hV0e : sqrt_controller_float4 pe (j / al) al dt = pe * (j / al) := by
    rw [sc_eq_lin b1 b2 b3 b4 c5 c6]
    exact sqrtc_clamp_lin _ hpe.1 (by rw [abs_le]; constructor <;> linarith) hk.1 (by linarith)
      (by linarith) hdt (by rw [hdt']; norm_num) (by rw [hdt']; norm_num)
  have hV0 := A32.mul_c hpe hk (Ra := 786 / 10000) (Rb := 20)
    (by rw [abs_le]; constructor <;> linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [capF]) (e := 3 / 10 ^ 5) (by norm_num)
  obtain ⟨hvcf, hvcv⟩ := Float32.sub_zero_val hω hdv hdv0
  have hvc : A32 (ω - dv) ω.toReal 0 := A32.of_val hvcf hvcv
  have hP := A32.mul_c hV0 hvc (Ra := 1571 / 1000) (Rb := 10)
    (by rw [abs_le]; constructor <;> linarith) hωb (by norm_num) le_rfl (by norm_num [capF])
    (e := 31 / 10 ^ 5) (by norm_num)
  have hPl := A32.lo hP
  have hPh := A32.hi hP
  simp only [tgtRoll]
  rw [hV0e]
  have hle : Float32.abs pe ≤ al / sq_float (j / al) := by
    rw [Float32.le_iff_toReal_le ((Float32.isFinite_abs pe).2 hpe.1) hld.1, Float32.toReal_abs,
      abs_le]
    constructor <;> linarith
  have hacc : A32 (sqrt_controller_accel pe (pe * (j / al)) (ω - dv) (j / al) al / (j / al))
      (-(sgn01 (is_positive_float (pe * (j / al) * (ω - dv))) * ω.toReal)) (5 / 10 ^ 6) := by
    cases hσ : is_positive_float (pe * (j / al) * (ω - dv))
    · rw [sca_eq_zero hσ]
      obtain ⟨zf0, zv⟩ := zf hL
      have := A32.div_c (A32.of_val zf0 zv) hk (Ra := 0) (m := 1999 / 100) (Q := 0) (by simp)
        (by norm_num) (by rw [abs_of_pos (by norm_num : (0:ℝ) < 20)]; norm_num) (by norm_num)
        (by simp) (by norm_num [capF]) (e := 5 / 10 ^ 6) (by norm_num)
      exact this.congr (by simp [sgn01])
    · rw [sca_eq_lin hσ b5 b6 hle]
      have hnk := A32.mul_c (A32.neg hk) hvc (Ra := 20) (Rb := 10) (by norm_num) hωb (by norm_num)
        le_rfl (by norm_num [capF]) (e := 43 / 10 ^ 6) (by norm_num)
      have := A32.div_c hnk hk (Ra := 200) (m := 1999 / 100) (Q := 1001 / 100)
        (by rw [abs_mul, abs_neg]; norm_num; linarith) (by norm_num)
        (by rw [abs_of_pos (by norm_num : (0:ℝ) < 20)]; norm_num) (by norm_num)
        (by rw [abs_div, abs_mul, abs_neg]; norm_num; linarith) (by norm_num [capF])
        (e := 5 / 10 ^ 6) (by norm_num)
      exact this.congr (by simp [sgn01]; ring)
  have hs0 := sgn01_nonneg (is_positive_float (pe * (j / al) * (ω - dv)))
  have hs1 := sgn01_le (is_positive_float (pe * (j / al) * (ω - dv)))
  refine ⟨is_positive_float (pe * (j / al) * (ω - dv)), ?_, ?_, ?_⟩
  · intro h
    have := (isPos_iff hP.1).1 h
    linarith
  · intro h
    have := (isPos_iff hP.1).not.1 (by rw [h]; simp)
    linarith
  generalize sgn01 (is_positive_float (pe * (j / al) * (ω - dv))) = sg at hacc hs0 hs1 ⊢
  generalize sqrt_controller_accel pe (pe * (j / al)) (ω - dv) (j / al) al / (j / al) = Q at hacc ⊢
  have hV1 := A32.add_c hV0 hacc (R := 1158 / 100) (by
    rw [abs_le]; constructor <;> nlinarith) (by norm_num [capF]) (e := 36 / 10 ^ 6) (by norm_num)
  obtain ⟨hvtf, hvtv⟩ := Float32.add_exact hdv hV1.1 hV1.1 (by rw [hdv0, zero_add])
  have hvt : A32 (dv + (pe * (j / al) + Q)) (er * 20 + -(sg * ω.toReal)) (36 / 10 ^ 6) :=
    ⟨hvtf, by rw [hvtv]; exact hV1.2⟩
  have hd := A32.sub_c hvt (A32.of_exact hω) (R := 2158 / 100) (by
    rw [abs_le]; constructor <;> nlinarith) (by norm_num [capF]) (e := 38 / 10 ^ 6) (by norm_num)
  have hX := A32.mul_c hd hk (Ra := 2158 / 100) (Rb := 20) (by
    rw [abs_le]; constructor <;> nlinarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [capF]) (e := 86 / 10 ^ 5) (by norm_num)
  obtain ⟨hlo, hhi⟩ := am_bounds ham ham'
  have hlh' : (-am).toReal ≤ am.toReal := by rw [Float32.toReal_neg]; linarith
  have hT0 := A32.cvl (Int32.toUInt32 334) hX hlo hhi hlh'
  obtain ⟨hT1f, hT1v⟩ := Float32.add_zero_val hT0.1 had had0
  have hT1 := A32.congr_x hT0 hT1f hT1v
  have hT := A32.cvl (Int32.toUInt32 341) hT1 hlo hhi hlh'
  rw [clampR_idem (by linarith)] at hT
  refine (hT.congr (by ring_nf)).mono (by norm_num)

/-! ## (a) Roll and pitch, linear zone -/

/-- The real roll/pitch law: `α' = α + clamp(clamp(α*, ±10π) - α, ±π/2)` (jerk step
`jerk·dt = (10π/0.05)/400 = π/2`). -/
def rpStep (αs α : ℝ) : ℝ :=
  α + clampR (-(Real.pi / 2)) (Real.pi / 2) (clampR (-(10 * Real.pi)) (10 * Real.pi) αs - α)

/-- The linear-zone command `α* = k_v (k_v e - (1 + σ) ω)` with `k_v = 1/input_tc = 20`. -/
def rpLin (σ : Bool) (e ω : ℝ) : ℝ := 20 * (20 * e - (1 + sgn01 σ) * ω)

/-- `ω' = ω + α'·dt`: the `float` step of the target rate, with `α'` within `10⁻³` of a value of
magnitude at most `34`. -/
theorem omega_step {ω a dt : Float32} {r ε : ℝ} (hω : ω.IsFinite) (hωb : |ω.toReal| ≤ 10)
    (ha : A32 a r ε) (hε : ε ≤ 1 / 10) (hr : |r| ≤ 34) (hdt : dt.IsFinite)
    (hdt' : dt.toReal = dtv) :
    A32 (ω + a * dt) (ω.toReal + r / 400) (ε / 400 + 2 / 10 ^ 6) := by
  have hε0 := A32.e_nonneg ha
  have hm := A32.mul_c ha (A32.of_val hdt hdt') (Ra := 34) (Rb := 1 / 400) hr (by norm_num [dtv])
    hε0 le_rfl (by norm_num [capF]; linarith) (e := ε / 400 + 1 / 10 ^ 6) (by norm_num; linarith)
  have hm' := A32.recenter hm (r' := r / 400) (d := 1 / 10 ^ 8) (by
    rw [show r * dtv - r / 400 = r * (dtv - 1 / 400) by ring, abs_mul]
    calc |r| * |dtv - 1 / 400| ≤ 34 * |dtv - 1 / 400| := by gcongr
      _ ≤ 1 / 10 ^ 8 := by norm_num [dtv])
  have hs := A32.add_c (A32.of_exact hω) hm' (R := 1009 / 100) (by
    have := abs_add_le ω.toReal (r / 400)
    rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 400)] at this
    linarith) (by norm_num [capF]; linarith) (e := ε / 400 + 2 / 10 ^ 6) (by norm_num; linarith)
  exact hs

/-- **(a) The roll/pitch law in the linear zone.** For the tuned parameters
(`max_ang_vel = radians(ATC_RATE_R_MAX = 0) = 0`, `accel_max` within `10⁻⁵` of
`10π = radians(1800)`, `input_tc = 0.05`, `dt = 1/400`, `desired_ang_vel` a zero), an error
`|e| ≤ 0.0785` (inside the linear distance `π/40 ≈ 0.07854`), `|ω| ≤ 10`, `|α| ≤ 32`:
`attitude_command_model e 0 ω α 0 accel_max 0.05 dt = (ω', α')` with

  `α' ≈ α + clamp(clamp(20(20 e − (1+σ) ω), ±10π) − α, ±π/2)` within `β = 10⁻³`,
  `ω' ≈ ω + α'/400` within `5·10⁻⁶` (`α'` the real law),

where `σ` (the Boolean `is_positive(vel_corr_cmd · ω)` of `sqrt_controller_accel`) is `true` only
if `20 e ω ≥ 2⁻²³ − 3.1·10⁻⁴` and `false` only if `20 e ω < 2⁻²³ + 3.1·10⁻⁴`. `β` is dominated by
`wrap_PI` (`1.4·10⁻⁶` on `e`, times `k_v² = 400`). -/
theorem rp_law_linear (hL : LibmSpec) (e dv ω α vm am tc dt : Float32)
    (he : e.IsFinite) (heb : |e.toReal| ≤ 785 / 10000)
    (hdv : dv.IsFinite) (hdv0 : dv.toReal = 0) (hω : ω.IsFinite) (hωb : |ω.toReal| ≤ 10)
    (hα : α.IsFinite) (hαb : |α.toReal| ≤ 32) (hvm : vm.IsFinite) (hvm0 : vm.toReal = 0)
    (ham : am.IsFinite) (ham' : |am.toReal - 10 * Real.pi| ≤ 1 / 10 ^ 5)
    (htc : tc.IsFinite) (htc' : tc.toReal = tcv) (hdt : dt.IsFinite) (hdt' : dt.toReal = dtv) :
    ∃ σ : Bool, (σ = true → 2 ^ (-23 : ℤ) - 31 / 10 ^ 5 ≤ 20 * e.toReal * ω.toReal) ∧
      (σ = false → 20 * e.toReal * ω.toReal < 2 ^ (-23 : ℤ) + 31 / 10 ^ 5) ∧
      A32 (AC_AttitudeControl_Multi.attitude_command_model e dv ω α vm am tc dt).2
        (rpStep (rpLin σ e.toReal ω.toReal) α.toReal) (1 / 10 ^ 3) ∧
      A32 (AC_AttitudeControl_Multi.attitude_command_model e dv ω α vm am tc dt).1
        (ω.toReal + rpStep (rpLin σ e.toReal ω.toReal) α.toReal / 400) (5 / 10 ^ 6) := by
  obtain ⟨p1, p2⟩ := pi_bounds
  obtain ⟨a1, a2⟩ := abs_le.1 ham'
  obtain ⟨hj, hhi, hlo⟩ := rp_consts hL ham ham' htc htc' hdt hdt'
  have hdtp : is_positive_float dt = true := isPos_true hdt (by rw [hdt']; norm_num)
  have hamp : is_positive_float am = true := isPos_true ham (by norm_num; linarith)
  have htcp : is_positive_float tc = true := isPos_true htc (by rw [htc']; norm_num)
  have hjp : is_positive_float (am / tc) = true := isPos_true hj.1 (by
    have := A32.lo hj; norm_num at this ⊢; linarith)
  have hnam : (-am).IsFinite := (Float32.isFinite_neg am).2 ham
  have hnvm : (-vm).IsFinite := (Float32.isFinite_neg vm).2 hvm
  have h1 : is_positive_float (-vm) = false :=
    isPos_false hnvm (by rw [Float32.toReal_neg, hvm0]; norm_num)
  have h2 : is_negative_float vm = false := isNeg_false hL hvm (by rw [hvm0]; norm_num)
  have h3 : is_negative_float (-am) = true := isNeg_true hL hnam (by
    rw [Float32.toReal_neg]; norm_num; linarith)
  have h6 : is_negative_float (-vm) = false :=
    isNeg_false hL hnvm (by rw [Float32.toReal_neg, hvm0]; norm_num)
  have h7 : is_positive_float vm = false := isPos_false hvm (by rw [hvm0]; norm_num)
  simp only [AC_AttitudeControl_Multi.attitude_command_model, Id.run, hdtp, hamp, htcp,
    Bool.not_true, Bool.false_eq_true, ite_false, id_pure_eq, shape_angle_vel_accel]
  rw [spva_roll h1 h2 h3 hamp hjp h6 h7]
  obtain ⟨hpe, _⟩ := posErr_near hL he (by linarith)
  generalize Float.toFloat32 (Float32.toFloat (Float.toFloat32 (0.0 : Float) +
      wrap_PI_float (e - Float.toFloat32 (0.0 : Float))) -
      Float32.toFloat (Float.toFloat32 (0.0 : Float))) = pe at hpe ⊢
  have hal : (if is_positive_float pe = true then - -am else am).IsFinite ∧
      (if is_positive_float pe = true then - -am else am).toReal = am.toReal := by
    split
    · exact ⟨(Float32.isFinite_neg _).2 hnam, by rw [Float32.toReal_neg, Float32.toReal_neg, neg_neg]⟩
    · exact ⟨ham, rfl⟩
  generalize (if is_positive_float pe = true then - -am else am) = al at hal ⊢
  obtain ⟨hzf, hz0⟩ := zf hL
  obtain ⟨σ, hσ1, hσ2, hT⟩ := tgtRoll_lin hL hpe heb hdv hdv0 hzf hz0 hω hωb ham ham' hj hal.1
    hal.2 hdt hdt'
  have hlh : (-(am / tc) * dt).toReal ≤ (am / tc * dt).toReal := by
    have := A32.hi hlo; have := A32.lo hhi; linarith
  have hcl := abs_clampR_le (L := 10 * Real.pi)
    (x := 20 * (20 * e.toReal - (1 + sgn01 σ) * ω.toReal)) (by linarith)
  have hS := shape_accel_law hjp hdtp hT hα hαb (by linarith) hlo hhi hlh (by linarith) (by linarith)
    (by norm_num) (by norm_num)
  have hS' : A32 (shape_accel (tgtRoll pe dv (Float.toFloat32 0.0) ω (-am) am (am / tc) al dt) α
      (am / tc) dt) (rpStep (rpLin σ e.toReal ω.toReal) α.toReal) (1 / 10 ^ 3) :=
    (hS.congr (by simp only [rpStep, rpLin])).mono (by norm_num)
  have hlaw : |rpStep (rpLin σ e.toReal ω.toReal) α.toReal| ≤ 34 := by
    unfold rpStep
    have := abs_clampR_le (L := Real.pi / 2)
      (x := clampR (-(10 * Real.pi)) (10 * Real.pi) (rpLin σ e.toReal ω.toReal) - α.toReal)
      (by linarith)
    have := abs_add_le α.toReal (clampR (-(Real.pi / 2)) (Real.pi / 2)
      (clampR (-(10 * Real.pi)) (10 * Real.pi) (rpLin σ e.toReal ω.toReal) - α.toReal))
    linarith
  exact ⟨σ, hσ1, hσ2, hS', (omega_step hω hωb hS' (by norm_num) hlaw hdt hdt').mono (by norm_num)⟩

/-! ## (b) Roll and pitch, square-root zone -/

theorem f64_unpack_int32_zero : (Int32.toFloat (0 : Int32)).toModel.unpack = .zero .positive := by
  f32_unpack

theorem A32.abs {x : Float32} {r e : ℝ} (h : A32 x r e) : A32 (Float32.abs x) |r| e :=
  ⟨(Float32.isFinite_abs x).2 h.1, by
    rw [Float32.toReal_abs]; exact (abs_abs_sub_abs_le_abs_sub _ _).trans h.2⟩

/-- `safe_sqrt` of a finite nonnegative float is its square root. -/
theorem safe_sqrt_eq (hL : LibmSpec) {v : Float32} (hv : v.IsFinite) (h0 : 0 ≤ v.toReal) :
    safe_sqrt_float v = Float32.sqrt v := by
  have hz : (Int32.toFloat (0 : Int32)).IsFinite := Float.isFinite_of_unpack_zero f64_unpack_int32_zero
  have hzv : (Int32.toFloat (0 : Int32)).toReal = 0 := Float.toReal_of_unpack_zero f64_unpack_int32_zero
  obtain ⟨f1, v1⟩ := hL.f32ToF64 v hv
  have hc : Float32.toFloat v ≥ Int32.toFloat (0 : Int32) := by
    rw [ge_iff_le, Float.le_iff_toReal_le hz f1, hzv, v1]; exact h0
  simp only [safe_sqrt_float, Id.run, id_pure_eq, decide_eq_true hc, ite_true]

/-- The square-root branch: `safe_sqrt(2.0 · accel_lim · d)` for `d` within `1.5·10⁻⁶` of
`x ∈ [0.03933, 0.2608]` is within `7.1·10⁻⁵` of `√(20π x)` (`2·accel_max = 20π`). -/
theorem sqrt_part (hL : LibmSpec) {d al am : Float32} {x : ℝ} (hd : A32 d x (15 / 10 ^ 7))
    (hx1 : 3933 / 100000 ≤ x) (hx2 : x ≤ 2608 / 10000) (ham' : |am.toReal - 10 * Real.pi| ≤ 1 / 10 ^ 5)
    (hal : al.IsFinite) (hal' : al.toReal = am.toReal) :
    A32 (safe_sqrt_float (Float.toFloat32 2.0 * al * d)) (Real.sqrt (20 * Real.pi * x))
      (71 / 10 ^ 6) := by
  obtain ⟨p1, p2⟩ := pi_bounds
  obtain ⟨a1, a2⟩ := abs_le.1 ham'
  obtain ⟨tf, tv⟩ := twof hL
  have hta := A32.mul_c (A32.of_val tf tv) (A32.of_val hal hal') (Ra := 2) (Rb := 3142 / 100)
    (by norm_num) (by rw [abs_le]; constructor <;> linarith) le_rfl le_rfl (by norm_num [capF])
    (e := 4 / 10 ^ 6) (by norm_num)
  have hta' := A32.recenter hta (r' := 20 * Real.pi) (d := 2 / 10 ^ 5) (by
    rw [abs_le]; constructor <;> linarith)
  have hp := A32.mul_c hta' hd (Ra := 6284 / 100) (Rb := 2608 / 10000)
    (by rw [abs_le]; constructor <;> linarith) (by rw [abs_le]; constructor <;> linarith)
    (by norm_num) (by norm_num) (by norm_num [capF]) (e := 11 / 10 ^ 5) (by norm_num)
  have hpl := A32.lo hp
  have hr0 : (247 / 100 : ℝ) ≤ 20 * Real.pi * x := by nlinarith
  rw [safe_sqrt_eq hL hp.1 (by nlinarith)]
  refine A32.sqrt_c hp (by nlinarith) hr0 (s0 := 157 / 100) (by norm_num)
    (Real.le_sqrt_of_sq_le (by norm_num)) (Rs := 41 / 10)
    ((Real.sqrt_le_left (by norm_num)).2 (by nlinarith))
    (by rw [abs_of_pos (by nlinarith)]; norm_num [capF]; nlinarith) (by norm_num)

/-- The final clamp of `sqrt_controller` is inactive for `|error| ≥ 0.07` and a correction rate of
at most `5` (`dt = 1/400`). -/
theorem sqrtc_clamp_big {pe cr dt : Float32} (line : UInt32) (hpe : pe.IsFinite)
    (hpe1 : 7 / 100 ≤ |pe.toReal|) (hpe2 : |pe.toReal| ≤ 1) (hcr : cr.IsFinite)
    (hcrb : |cr.toReal| ≤ 5) (hdt : dt.IsFinite) (hdt' : dt.toReal = dtv) :
    constrain_value_line_float cr (-(Float32.abs pe) / dt) (Float32.abs pe / dt) line = cr := by
  have hab := (Float32.isFinite_abs pe).2 hpe
  have hnab := (Float32.isFinite_neg _).2 hab
  have habv : (Float32.abs pe).toReal = |pe.toReal| := Float32.toReal_abs pe
  have hd0 : dt.toReal ≠ 0 := by rw [hdt']; norm_num
  have h1 := A32.div_c (A32.of_val hab habv) (A32.of_val hdt hdt') (Ra := 1) (m := 1 / 401)
    (Q := 401) (by rw [abs_abs]; exact hpe2) (by norm_num) (by norm_num [dtv]) le_rfl
    (by rw [abs_div, abs_abs, abs_of_pos (by norm_num : (0:ℝ) < dtv), div_le_iff₀ (by norm_num)]
        norm_num [dtv]; linarith)
    (by norm_num [capF]) (e := 1 / 10 ^ 4) (by norm_num)
  have h2 := A32.div_c (A32.of_val hnab (by rw [Float32.toReal_neg, habv])) (A32.of_val hdt hdt')
    (Ra := 1) (m := 1 / 401) (Q := 401) (by rw [abs_neg, abs_abs]; exact hpe2) (by norm_num)
    (by norm_num [dtv]) le_rfl
    (by rw [abs_div, abs_neg, abs_abs, abs_of_pos (by norm_num : (0:ℝ) < dtv),
          div_le_iff₀ (by norm_num)]; norm_num [dtv]; linarith)
    (by norm_num [capF]) (e := 1 / 10 ^ 4) (by norm_num)
  have l1 := A32.lo h1
  have l2 := A32.hi h2
  have q1 : 28 ≤ |pe.toReal| / dtv := by rw [le_div_iff₀ (by norm_num)]; norm_num [dtv]; linarith
  have q2 : -|pe.toReal| / dtv ≤ -28 := by rw [neg_div]; linarith
  obtain ⟨c1, c2⟩ := abs_le.1 hcrb
  exact constrain_inside line hcr h2.1 h1.1 (by linarith) (by linarith)

/-- The signed square-root velocity `sign(e) √(2·10π (|e| − π/80))` (`π/80` is half the linear
distance `π/40`). -/
def vSq (e : ℝ) : ℝ :=
  if 0 ≤ e then Real.sqrt (20 * Real.pi * (e - Real.pi / 80))
  else -Real.sqrt (20 * Real.pi * (-e - Real.pi / 80))

theorem vSq_bounds {e : ℝ} (h1 : 786 / 10000 ≤ |e|) (h2 : |e| ≤ 3 / 10) :
    157 / 100 ≤ |vSq e| ∧ |vSq e| ≤ 41 / 10 := by
  obtain ⟨p1, p2⟩ := pi_bounds
  have key : ∀ y : ℝ, 786 / 10000 ≤ y → y ≤ 3 / 10 →
      157 / 100 ≤ Real.sqrt (20 * Real.pi * (y - Real.pi / 80)) ∧
        Real.sqrt (20 * Real.pi * (y - Real.pi / 80)) ≤ 41 / 10 := by
    intro y hy1 hy2
    exact ⟨Real.le_sqrt_of_sq_le (by nlinarith), (Real.sqrt_le_left (by norm_num)).2 (by nlinarith)⟩
  unfold vSq
  split
  · rename_i h
    rw [abs_of_nonneg h] at h1 h2
    rw [abs_of_nonneg (Real.sqrt_nonneg _)]
    exact key e h1 h2
  · rename_i h
    rw [abs_of_neg (not_le.1 h)] at h1 h2
    rw [abs_neg, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact key (-e) h1 h2

/-- `sqrt_controller(e, k_v, accel_lim, dt)` on the square-root zone `0.0786 ≤ |e| ≤ 0.3`. -/
theorem sc_sqrt_zone (hL : LibmSpec) {pe am j al dt : Float32} {er : ℝ}
    (hpe : A32 pe er (14 / 10 ^ 7)) (her1 : 786 / 10000 ≤ |er|) (her2 : |er| ≤ 3 / 10)
    (ham : am.IsFinite) (ham' : |am.toReal - 10 * Real.pi| ≤ 1 / 10 ^ 5)
    (hj : A32 j (am.toReal / tcv) (38 / 10 ^ 6)) (hal : al.IsFinite) (hal' : al.toReal = am.toReal)
    (hdt : dt.IsFinite) (hdt' : dt.toReal = dtv) :
    A32 (sqrt_controller_float4 pe (j / al) al dt) (vSq er) (71 / 10 ^ 6) := by
  obtain ⟨p1, p2⟩ := pi_bounds
  obtain ⟨a1, a2⟩ := abs_le.1 ham'
  obtain ⟨hk, _, hld⟩ := rp_gain ham ham' hj hal hal'
  have hpl := A32.lo hpe
  have hph := A32.hi hpe
  have hkl := A32.lo hk
  have hll := A32.lo hld
  have hlh := A32.hi hld
  have b1 : is_negative_float al = false := isNeg_false hL hal (by rw [hal']; norm_num; linarith)
  have b2 : is_zero_float al = false :=
    isZero_false hal (by rw [hal', abs_of_pos (by linarith)]; norm_num; linarith)
  have b3 : is_zero_float (j / al) = false :=
    isZero_false hk.1 (by rw [abs_of_pos (by linarith)]; norm_num; linarith)
  have b4 : is_positive_float dt = true := isPos_true hdt (by rw [hdt']; norm_num)
  obtain ⟨tf, tv⟩ := twof hL
  have hld2 := A32.div_c hld (A32.of_val tf tv) (Ra := 786 / 10000) (m := 2) (Q := 393 / 10000)
    (by rw [abs_le]; constructor <;> linarith) (by norm_num) (by norm_num) le_rfl
    (by rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 2), div_le_iff₀ (by norm_num), abs_le]
        constructor <;> linarith)
    (by norm_num [capF]) (e := 6 / 10 ^ 8) (by norm_num)
  have hl2l := A32.lo hld2
  have hl2h := A32.hi hld2
  have hpe1 : 7 / 100 ≤ |pe.toReal| := by
    rcases le_or_gt 0 er with h | h
    · rw [abs_of_nonneg h] at her1; rw [abs_of_pos (by linarith)]; linarith
    · rw [abs_of_neg h] at her1; rw [abs_of_neg (by linarith)]; linarith
  have hpe2 : |pe.toReal| ≤ 1 := by rw [abs_le]; constructor <;> linarith [abs_le.1 her2]
  unfold vSq
  split
  · rename_i h0
    rw [abs_of_nonneg h0] at her1 her2
    have c5 : pe > al / sq_float (j / al) := by
      rw [gt_iff_lt, Float32.lt_iff_toReal_lt hld.1 hpe.1]; linarith
    rw [sc_eq_pos b1 b2 b3 b4 c5]
    have hd := A32.sub_c hpe hld2 (R := 2608 / 10000) (by rw [abs_le]; constructor <;> linarith)
      (by norm_num [capF]) (e := 15 / 10 ^ 7) (by norm_num)
    have hs := sqrt_part hL hd (by linarith) (by linarith) ham' hal hal'
    rw [sqrtc_clamp_big _ hpe.1 hpe1 hpe2 hs.1 (by
      have := A32.abs_le hs; rw [abs_of_nonneg (Real.sqrt_nonneg _)] at this
      have := (Real.sqrt_le_left (by norm_num : (0:ℝ) ≤ 41 / 10)).2
        (show 20 * Real.pi * (er - Real.pi / 40 / 2) ≤ (41 / 10) ^ 2 by nlinarith)
      linarith) hdt hdt']
    exact hs.congr (by ring_nf)
  · rename_i h0
    rw [abs_of_neg (not_le.1 h0)] at her1 her2
    have c5 : ¬ pe > al / sq_float (j / al) := by
      rw [gt_iff_lt, Float32.lt_iff_toReal_lt hld.1 hpe.1]; linarith
    have c6 : pe < -(al / sq_float (j / al)) := by
      rw [Float32.lt_iff_toReal_lt hpe.1 ((Float32.isFinite_neg _).2 hld.1), Float32.toReal_neg]
      linarith
    rw [sc_eq_neg b1 b2 b3 b4 c5 c6]
    have hd := A32.sub_c (A32.neg hpe) hld2 (R := 2608 / 10000)
      (by rw [abs_le]; constructor <;> linarith)
      (by norm_num [capF]) (e := 15 / 10 ^ 7) (by norm_num)
    have hs := sqrt_part hL hd (by linarith) (by linarith) ham' hal hal'
    have hns := A32.neg hs
    rw [sqrtc_clamp_big _ hpe.1 hpe1 hpe2 hns.1 (by
      have := A32.abs_le hns
      rw [abs_neg, abs_of_nonneg (Real.sqrt_nonneg _)] at this
      have := (Real.sqrt_le_left (by norm_num : (0:ℝ) ≤ 41 / 10)).2
        (show 20 * Real.pi * (-er - Real.pi / 40 / 2) ≤ (41 / 10) ^ 2 by nlinarith)
      linarith) hdt hdt']
    exact hns.congr (by ring_nf)

/-- The square-root-zone command `α* = k_v (v_s − ω) − σ (accel_max/|v_s|) ω` (`k_v = 20`,
`accel_max = 10π`, `v_s = vSq e`). -/
def rpSq (σ : Bool) (e ω : ℝ) : ℝ :=
  20 * (vSq e - ω) - sgn01 σ * (10 * Real.pi / |vSq e|) * ω

/-- **The roll/pitch acceleration target, square-root zone** (`0.0786 ≤ |e| ≤ 0.3`,
`|ω| ≤ 10`): `clamp(rpSq σ e ω, ±10π)` within `1.15·10⁻²`; `σ` agrees with the real product
`v_s ω ≥ 2⁻²³` up to `7.2·10⁻⁴`. -/
theorem tgtRoll_sqrt (hL : LibmSpec) {pe dv ad ω am j al dt : Float32} {er : ℝ}
    (hpe : A32 pe er (14 / 10 ^ 7)) (her1 : 786 / 10000 ≤ |er|) (her2 : |er| ≤ 3 / 10)
    (hdv : dv.IsFinite) (hdv0 : dv.toReal = 0) (had : ad.IsFinite) (had0 : ad.toReal = 0)
    (hω : ω.IsFinite) (hωb : |ω.toReal| ≤ 10)
    (ham : am.IsFinite) (ham' : |am.toReal - 10 * Real.pi| ≤ 1 / 10 ^ 5)
    (hj : A32 j (am.toReal / tcv) (38 / 10 ^ 6)) (hal : al.IsFinite) (hal' : al.toReal = am.toReal)
    (hdt : dt.IsFinite) (hdt' : dt.toReal = dtv) :
    ∃ σ : Bool, (σ = true → 2 ^ (-23 : ℤ) - 72 / 10 ^ 5 ≤ vSq er * ω.toReal) ∧
      (σ = false → vSq er * ω.toReal < 2 ^ (-23 : ℤ) + 72 / 10 ^ 5) ∧
      A32 (tgtRoll pe dv ad ω (-am) am j al dt)
        (clampR (-(10 * Real.pi)) (10 * Real.pi) (rpSq σ er ω.toReal)) (115 / 10 ^ 4) := by
  obtain ⟨p1, p2⟩ := pi_bounds
  obtain ⟨a1, a2⟩ := abs_le.1 ham'
  obtain ⟨w1, w2⟩ := abs_le.1 hωb
  obtain ⟨hk, _, hld⟩ := rp_gain ham ham' hj hal hal'
  obtain ⟨v1, v2⟩ := vSq_bounds her1 her2
  have hpl := A32.lo hpe
  have hph := A32.hi hpe
  have hkl := A32.lo hk
  have hkh := A32.hi hk
  have hll := A32.lo hld
  have hlh := A32.hi hld
  have b5 : is_positive_float al = true := isPos_true hal (by rw [hal']; norm_num; linarith)
  have b6 : is_positive_float (j / al) = true := isPos_true hk.1 (by norm_num; linarith)
  have hV0 := sc_sqrt_zone hL hpe her1 her2 ham ham' hj hal hal' hdt hdt'
  obtain ⟨hvcf, hvcv⟩ := Float32.sub_zero_val hω hdv hdv0
  have hvc : A32 (ω - dv) ω.toReal 0 := A32.of_val hvcf hvcv
  have hP := A32.mul_c hV0 hvc (Ra := 41 / 10) (Rb := 10) v2 hωb (by norm_num) le_rfl
    (by norm_num [capF]) (e := 72 / 10 ^ 5) (by norm_num)
  have hPl := A32.lo hP
  have hPh := A32.hi hP
  simp only [tgtRoll]
  generalize sqrt_controller_float4 pe (j / al) al dt = V0 at hV0 hP hPl hPh ⊢
  have hle : ¬ Float32.abs pe ≤ al / sq_float (j / al) := by
    rw [Float32.le_iff_toReal_le ((Float32.isFinite_abs pe).2 hpe.1) hld.1, Float32.toReal_abs]
    intro h
    rcases le_or_gt 0 er with h0 | h0
    · rw [abs_of_nonneg h0] at her1
      have := le_abs_self pe.toReal; linarith
    · rw [abs_of_neg h0] at her1
      have := neg_abs_le pe.toReal; linarith
  have hV0a := A32.abs hV0
  have hV0al := A32.lo hV0a
  have hz : is_zero_float V0 = false := isZero_false hV0.1 (by
    rw [← Float32.toReal_abs]; norm_num; linarith)
  have hacc : A32 (sqrt_controller_accel pe V0 (ω - dv) (j / al) al / (j / al))
      (-(sgn01 (is_positive_float (V0 * (ω - dv))) * (10 * Real.pi / |vSq er| * ω.toReal / 20)))
      (47 / 10 ^ 5) := by
    cases hσ : is_positive_float (V0 * (ω - dv))
    · rw [sca_eq_zero hσ]
      obtain ⟨zf0, zv⟩ := zf hL
      have := A32.div_c (A32.of_val zf0 zv) hk (Ra := 0) (m := 1999 / 100) (Q := 0) (by simp)
        (by norm_num) (by rw [abs_of_pos (by norm_num : (0:ℝ) < 20)]; norm_num) (by norm_num)
        (by simp) (by norm_num [capF]) (e := 47 / 10 ^ 5) (by norm_num)
      exact this.congr (by simp [sgn01])
    · rw [sca_eq_sqrt hσ b5 b6 hle hz]
      have hq := A32.div_c (A32.of_val hal hal') hV0a (Ra := 3142 / 100) (m := 15699 / 10000)
        (Q := 2002 / 100) (by rw [abs_le]; constructor <;> linarith) (by norm_num)
        (by rw [abs_abs]; linarith) (by norm_num)
        (by rw [abs_div, abs_abs, div_le_iff₀ (by linarith)]
            rw [abs_le] at *; constructor <;> nlinarith)
        (by norm_num [capF]) (e := 91 / 10 ^ 5) (by norm_num)
      have hq' := A32.recenter hq (r' := 10 * Real.pi / |vSq er|) (d := 1 / 10 ^ 5) (by
        rw [← sub_div, abs_div, abs_abs, div_le_iff₀ (by linarith)]; nlinarith)
      have hq10 : |(10 * Real.pi / |vSq er|)| ≤ 2002 / 100 := by
        rw [abs_div, abs_abs, div_le_iff₀ (by linarith), abs_of_pos (by linarith)]; nlinarith
      have hm := A32.mul_c (A32.neg hq') hvc (Ra := 2002 / 100) (Rb := 10)
        (by rw [abs_neg]; exact hq10) hωb (by norm_num) le_rfl (by norm_num [capF])
        (e := 93 / 10 ^ 4) (by norm_num)
      have := A32.div_c hm hk (Ra := 201) (m := 1999 / 100) (Q := 1006 / 100)
        (by rw [abs_mul, abs_neg]
            have := mul_le_mul hq10 hωb (abs_nonneg _) (by norm_num); linarith)
        (by norm_num) (by rw [abs_of_pos (by norm_num : (0:ℝ) < 20)]; norm_num) (by norm_num)
        (by rw [abs_div, abs_mul, abs_neg, abs_of_pos (by norm_num : (0:ℝ) < 20)]
            have := mul_le_mul hq10 hωb (abs_nonneg _) (by norm_num); linarith)
        (by norm_num [capF]) (e := 47 / 10 ^ 5) (by norm_num)
      exact this.congr (by simp [sgn01]; ring)
  have hs0 := sgn01_nonneg (is_positive_float (V0 * (ω - dv)))
  have hs1 := sgn01_le (is_positive_float (V0 * (ω - dv)))
  have hq10 : |(10 * Real.pi / |vSq er| * ω.toReal / 20)| ≤ 1001 / 100 := by
    rw [abs_div, abs_mul, abs_div, abs_abs, abs_of_pos (by linarith : (0:ℝ) < 10 * Real.pi),
      abs_of_pos (by norm_num : (0:ℝ) < 20), div_le_iff₀ (by norm_num)]
    have h1 : 10 * Real.pi / |vSq er| ≤ 2002 / 100 := by
      rw [div_le_iff₀ (by linarith)]; nlinarith
    have := mul_le_mul h1 hωb (abs_nonneg _) (by norm_num); linarith
  refine ⟨is_positive_float (V0 * (ω - dv)), ?_, ?_, ?_⟩
  · intro h
    have h' := (isPos_iff hP.1).1 h
    by_contra hc
    exact absurd (lt_of_le_of_lt h' (lt_of_le_of_lt hPh (by linarith))) (lt_irrefl _)
  · intro h
    have h' := not_le.1 ((isPos_iff hP.1).not.1 (by rw [h]; simp))
    by_contra hc
    exact absurd (lt_of_lt_of_le h' (le_trans (by linarith) hPl)) (lt_irrefl _)
  unfold rpSq
  generalize sgn01 (is_positive_float (V0 * (ω - dv))) = sg at hacc hs0 hs1 ⊢
  generalize sqrt_controller_accel pe V0 (ω - dv) (j / al) al / (j / al) = Q at hacc ⊢
  have hsq : |sg * (10 * Real.pi / |vSq er| * ω.toReal / 20)| ≤ 1001 / 100 := by
    rw [abs_mul, abs_of_nonneg hs0]
    have := mul_le_mul hs1 hq10 (abs_nonneg _) (by norm_num); linarith
  obtain ⟨q1, q2⟩ := abs_le.1 hsq
  obtain ⟨vv1, vv2⟩ := abs_le.1 v2
  have hV1 := A32.add_c hV0 hacc (R := 1412 / 100) (by
    rw [abs_le]; constructor <;> linarith) (by norm_num [capF]) (e := 55 / 10 ^ 5) (by norm_num)
  obtain ⟨hvtf, hvtv⟩ := Float32.add_exact hdv hV1.1 hV1.1 (by rw [hdv0, zero_add])
  have hvt := A32.congr_x hV1 hvtf hvtv
  have hd := A32.sub_c hvt (A32.of_exact hω) (R := 2412 / 100) (by
    rw [abs_le]; constructor <;> linarith) (by norm_num [capF]) (e := 56 / 10 ^ 5) (by norm_num)
  have hX := A32.mul_c hd hk (Ra := 2412 / 100) (Rb := 20) (by
    rw [abs_le]; constructor <;> linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [capF]) (e := 114 / 10 ^ 4) (by norm_num)
  obtain ⟨hlo, hhi⟩ := am_bounds ham ham'
  have hlh' : (-am).toReal ≤ am.toReal := by rw [Float32.toReal_neg]; linarith
  have hT0 := A32.cvl (Int32.toUInt32 334) hX hlo hhi hlh'
  obtain ⟨hT1f, hT1v⟩ := Float32.add_zero_val hT0.1 had had0
  have hT1 := A32.congr_x hT0 hT1f hT1v
  have hT := A32.cvl (Int32.toUInt32 341) hT1 hlo hhi hlh'
  rw [clampR_idem (by linarith)] at hT
  refine (hT.congr (by ring_nf)).mono (by norm_num)

/-- **(b) The roll/pitch law in the square-root zone** `0.0786 ≤ |e| ≤ 0.3` (same parameters
and `|ω| ≤ 10`, `|α| ≤ 32`): with `v_s = sign(e) √(2·10π (|e| − π/80))` (`vSq`),

  `α' ≈ α + clamp(clamp(20 (v_s − ω) − σ (10π/|v_s|) ω, ±10π) − α, ±π/2)` within `β = 1.2·10⁻²`,
  `ω' ≈ ω + α'/400` within `4·10⁻⁵`,

`σ` agreeing with `v_s ω ≥ 2⁻²³` up to `7.2·10⁻⁴`. `β` is dominated by the `wrap_PI` error of `e`
amplified through `√` and the `accel_max/|v_s|` term (`k_v δv + accel_max |ω| δv / v_s²`). -/
theorem rp_law_sqrt (hL : LibmSpec) (e dv ω α vm am tc dt : Float32)
    (he : e.IsFinite) (heb1 : 786 / 10000 ≤ |e.toReal|) (heb : |e.toReal| ≤ 3 / 10)
    (hdv : dv.IsFinite) (hdv0 : dv.toReal = 0) (hω : ω.IsFinite) (hωb : |ω.toReal| ≤ 10)
    (hα : α.IsFinite) (hαb : |α.toReal| ≤ 32) (hvm : vm.IsFinite) (hvm0 : vm.toReal = 0)
    (ham : am.IsFinite) (ham' : |am.toReal - 10 * Real.pi| ≤ 1 / 10 ^ 5)
    (htc : tc.IsFinite) (htc' : tc.toReal = tcv) (hdt : dt.IsFinite) (hdt' : dt.toReal = dtv) :
    ∃ σ : Bool, (σ = true → 2 ^ (-23 : ℤ) - 72 / 10 ^ 5 ≤ vSq e.toReal * ω.toReal) ∧
      (σ = false → vSq e.toReal * ω.toReal < 2 ^ (-23 : ℤ) + 72 / 10 ^ 5) ∧
      A32 (AC_AttitudeControl_Multi.attitude_command_model e dv ω α vm am tc dt).2
        (rpStep (rpSq σ e.toReal ω.toReal) α.toReal) (12 / 10 ^ 3) ∧
      A32 (AC_AttitudeControl_Multi.attitude_command_model e dv ω α vm am tc dt).1
        (ω.toReal + rpStep (rpSq σ e.toReal ω.toReal) α.toReal / 400) (4 / 10 ^ 5) := by
  obtain ⟨p1, p2⟩ := pi_bounds
  obtain ⟨a1, a2⟩ := abs_le.1 ham'
  obtain ⟨hj, hhi, hlo⟩ := rp_consts hL ham ham' htc htc' hdt hdt'
  have hdtp : is_positive_float dt = true := isPos_true hdt (by rw [hdt']; norm_num)
  have hamp : is_positive_float am = true := isPos_true ham (by norm_num; linarith)
  have htcp : is_positive_float tc = true := isPos_true htc (by rw [htc']; norm_num)
  have hjp : is_positive_float (am / tc) = true := isPos_true hj.1 (by
    have := A32.lo hj; norm_num at this ⊢; linarith)
  have hnam : (-am).IsFinite := (Float32.isFinite_neg am).2 ham
  have hnvm : (-vm).IsFinite := (Float32.isFinite_neg vm).2 hvm
  have h1 : is_positive_float (-vm) = false :=
    isPos_false hnvm (by rw [Float32.toReal_neg, hvm0]; norm_num)
  have h2 : is_negative_float vm = false := isNeg_false hL hvm (by rw [hvm0]; norm_num)
  have h3 : is_negative_float (-am) = true := isNeg_true hL hnam (by
    rw [Float32.toReal_neg]; norm_num; linarith)
  have h6 : is_negative_float (-vm) = false :=
    isNeg_false hL hnvm (by rw [Float32.toReal_neg, hvm0]; norm_num)
  have h7 : is_positive_float vm = false := isPos_false hvm (by rw [hvm0]; norm_num)
  simp only [AC_AttitudeControl_Multi.attitude_command_model, Id.run, hdtp, hamp, htcp,
    Bool.not_true, Bool.false_eq_true, ite_false, id_pure_eq, shape_angle_vel_accel]
  rw [spva_roll h1 h2 h3 hamp hjp h6 h7]
  obtain ⟨hpe, _⟩ := posErr_near hL he (by linarith)
  generalize Float.toFloat32 (Float32.toFloat (Float.toFloat32 (0.0 : Float) +
      wrap_PI_float (e - Float.toFloat32 (0.0 : Float))) -
      Float32.toFloat (Float.toFloat32 (0.0 : Float))) = pe at hpe ⊢
  have hal : (if is_positive_float pe = true then - -am else am).IsFinite ∧
      (if is_positive_float pe = true then - -am else am).toReal = am.toReal := by
    split
    · exact ⟨(Float32.isFinite_neg _).2 hnam, by rw [Float32.toReal_neg, Float32.toReal_neg, neg_neg]⟩
    · exact ⟨ham, rfl⟩
  generalize (if is_positive_float pe = true then - -am else am) = al at hal ⊢
  obtain ⟨hzf, hz0⟩ := zf hL
  obtain ⟨σ, hσ1, hσ2, hT⟩ := tgtRoll_sqrt hL hpe heb1 heb hdv hdv0 hzf hz0 hω hωb ham ham' hj
    hal.1 hal.2 hdt hdt'
  have hlh : (-(am / tc) * dt).toReal ≤ (am / tc * dt).toReal := by
    have := A32.hi hlo; have := A32.lo hhi; linarith
  have hcl := abs_clampR_le (L := 10 * Real.pi) (x := rpSq σ e.toReal ω.toReal) (by linarith)
  have hS := shape_accel_law hjp hdtp hT hα hαb (by linarith) hlo hhi hlh (by linarith) (by linarith)
    (by norm_num) (by norm_num)
  have hS' : A32 (shape_accel (tgtRoll pe dv (Float.toFloat32 0.0) ω (-am) am (am / tc) al dt) α
      (am / tc) dt) (rpStep (rpSq σ e.toReal ω.toReal) α.toReal) (12 / 10 ^ 3) :=
    (hS.congr (by simp only [rpStep])).mono (by norm_num)
  have hlaw : |rpStep (rpSq σ e.toReal ω.toReal) α.toReal| ≤ 34 := by
    unfold rpStep
    have := abs_clampR_le (L := Real.pi / 2)
      (x := clampR (-(10 * Real.pi)) (10 * Real.pi) (rpSq σ e.toReal ω.toReal) - α.toReal)
      (by linarith)
    have := abs_add_le α.toReal (clampR (-(Real.pi / 2)) (Real.pi / 2)
      (clampR (-(10 * Real.pi)) (10 * Real.pi) (rpSq σ e.toReal ω.toReal) - α.toReal))
    linarith
  exact ⟨σ, hσ1, hσ2, hS', (omega_step hω hωb hS' (by norm_num) hlaw hdt hdt').mono (by norm_num)⟩

/-! ## (d) Yaw, linear zone -/

/-- `MIN(MAX(x, lo), hi)` of approximations: the real clamp. -/
theorem A32.minmax {x lo hi : Float32} {r l h ε εl εh : ℝ} (hx : A32 x r ε) (hl : A32 lo l εl)
    (hh : A32 hi h εh) (hlh : lo.toReal ≤ hi.toReal) :
    A32 (MIN_float2 (MAX_float2 x lo) hi) (clampR l h r) (ε + εl + εh) := by
  have e1 : MAX_float2 x lo = if x > lo then x else lo := rfl
  obtain ⟨f1, v1⟩ := Float32.ite_gt_max hx.1 hl.1
  rw [← e1] at f1 v1
  have e2 : MIN_float2 (MAX_float2 x lo) hi =
      if MAX_float2 x lo < hi then MAX_float2 x lo else hi := rfl
  obtain ⟨f2, v2⟩ := Float32.ite_lt_min f1 hh.1
  rw [← e2] at f2 v2
  refine ⟨f2, ?_⟩
  rw [v2, v1]
  have hc : min (max x.toReal lo.toReal) hi.toReal = clampR lo.toReal hi.toReal x.toReal := by
    unfold clampR
    rcases le_total x.toReal lo.toReal with h1 | h1
    · rw [max_eq_right h1, min_eq_left hlh, min_eq_right (h1.trans hlh), max_eq_left h1]
    · rw [max_eq_left h1]
      rcases le_total x.toReal hi.toReal with h2 | h2
      · rw [min_eq_left h2, min_eq_right h2, max_eq_right h1]
      · rw [min_eq_right h2, min_eq_left h2, max_eq_right hlh]
  rw [hc]
  have := clampR_lip lo.toReal hi.toReal x.toReal l h r
  linarith [hl.2, hh.2, hx.2]

/-- Yaw: `k_v = jerk / accel_lim ≈ 1/(10 dt) ≈ 40` and the linear distance
`accel_lim / k_v² ≈ (3π/2)/1600 = 3π/3200 ≈ 0.002945`. -/
theorem yaw_gain {am j al : Float32} (ham' : |am.toReal - 3 * Real.pi / 2| ≤ 1 / 10 ^ 5)
    (hj : A32 j (am.toReal / (dtv * 10)) (3 / 10 ^ 5)) (hal : al.IsFinite)
    (hal' : al.toReal = am.toReal) :
    A32 (j / al) 40 (1 / 10 ^ 5) ∧ A32 (sq_float (j / al)) 1600 (9 / 10 ^ 4) ∧
      A32 (al / sq_float (j / al)) (3 * Real.pi / 3200) (1 / 10 ^ 8) := by
  obtain ⟨p1, p2⟩ := pi_bounds
  obtain ⟨a1, a2⟩ := abs_le.1 ham'
  have hA : A32 al am.toReal 0 := A32.of_val hal hal'
  have ha0 : am.toReal ≠ 0 := by intro h; rw [h] at a1; linarith
  have hq : am.toReal / (dtv * 10) / am.toReal = 1 / (dtv * 10) := by field_simp
  have hk0 := A32.div_c hj hA (Ra := 1886 / 10) (m := 4712 / 1000) (Q := 4001 / 100)
    (by rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < dtv * 10), div_le_iff₀ (by norm_num),
          abs_le]
        constructor <;> norm_num [dtv] <;> linarith)
    (by norm_num) (by rw [abs_of_pos (by linarith)]; linarith) le_rfl
    (by rw [hq]; norm_num [dtv]) (by norm_num [capF]) (e := 9 / 10 ^ 6) (by norm_num)
  rw [hq] at hk0
  have hk : A32 (j / al) 40 (1 / 10 ^ 5) :=
    (A32.recenter hk0 (d := 1 / 10 ^ 6) (by norm_num [dtv])).mono (by norm_num)
  have hsq0 := A32.mul_c hk hk (Ra := 40) (Rb := 40) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num [capF]) (e := 9 / 10 ^ 4) (by norm_num)
  have hsq : A32 (sq_float (j / al)) 1600 (9 / 10 ^ 4) := by
    have e : sq_float (j / al) = j / al * (j / al) := rfl
    rw [e]; exact hsq0.congr (by norm_num)
  have hld0 := A32.div_c hA hsq (Ra := 47125 / 10000) (m := 15999 / 10) (Q := 295 / 100000)
    (by rw [abs_le]; constructor <;> linarith) (by norm_num) (by norm_num) (by norm_num)
    (by rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 1600), div_le_iff₀ (by norm_num), abs_le]
        constructor <;> linarith)
    (by norm_num [capF]) (e := 2 / 10 ^ 9) (by norm_num)
  refine ⟨hk, hsq, (A32.recenter hld0 (d := 7 / 10 ^ 9) ?_).mono (by norm_num)⟩
  rw [show am.toReal / 1600 - 3 * Real.pi / 3200 = (am.toReal - 3 * Real.pi / 2) / 1600 by ring,
    abs_div, abs_of_pos (by norm_num : (0:ℝ) < 1600), div_le_iff₀ (by norm_num)]
  linarith

/-- The yaw command of the linear zone, with both velocity limits `±S` (`S = π/3`, the slew):
`α* = 40 (clamp(ψ̇ + clamp(40 e − σ (ω − ψ̇), ±S), ±S) − ω)` (`k_v = 1/(10 dt) = 40`). -/
def yawCmd (σ : Bool) (e ψd ω : ℝ) : ℝ :=
  40 * (clampR (-(Real.pi / 3)) (Real.pi / 3)
    (ψd + clampR (-(Real.pi / 3)) (Real.pi / 3) (40 * e - sgn01 σ * (ω - ψd))) - ω)

/-- The real yaw step: `α' = α + clamp(clamp(α*, ±3π/2) − α, ±3π/20)`. -/
def yawStep (αs α : ℝ) : ℝ :=
  α + clampR (-(3 * Real.pi / 20)) (3 * Real.pi / 20)
    (clampR (-(3 * Real.pi / 2)) (3 * Real.pi / 2) αs - α)

/-- **The yaw acceleration target, linear zone** (`|e| ≤ 0.0029 < 3π/3200`, `|ψ̇| ≤ 2`,
`|ω| ≤ 4`): `clamp(yawCmd σ e ψ̇ ω, ±3π/2)` within `3·10⁻³`. -/
theorem tgtYaw_lin (hL : LibmSpec) {pe dv ad ω vm am j al dt : Float32} {er : ℝ}
    (hpe : A32 pe er (14 / 10 ^ 7)) (her : |er| ≤ 29 / 10000)
    (hdv : dv.IsFinite) (hdvb : |dv.toReal| ≤ 2) (had : ad.IsFinite) (had0 : ad.toReal = 0)
    (hω : ω.IsFinite) (hωb : |ω.toReal| ≤ 4)
    (hvm : vm.IsFinite) (hvm' : |vm.toReal - Real.pi / 3| ≤ 1 / 10 ^ 6)
    (ham : am.IsFinite) (ham' : |am.toReal - 3 * Real.pi / 2| ≤ 1 / 10 ^ 5)
    (hj : A32 j (am.toReal / (dtv * 10)) (3 / 10 ^ 5)) (hal : al.IsFinite)
    (hal' : al.toReal = am.toReal) (hdt : dt.IsFinite) (hdt' : dt.toReal = dtv) :
    ∃ σ : Bool, (σ = true → 2 ^ (-23 : ℤ) - 35 / 10 ^ 5 ≤ 40 * er * (ω.toReal - dv.toReal)) ∧
      (σ = false → 40 * er * (ω.toReal - dv.toReal) < 2 ^ (-23 : ℤ) + 35 / 10 ^ 5) ∧
      A32 (tgtYaw pe dv ad ω (-vm) vm (-am) am j al dt)
        (clampR (-(3 * Real.pi / 2)) (3 * Real.pi / 2) (yawCmd σ er dv.toReal ω.toReal))
        (3 / 10 ^ 3) := by
  obtain ⟨p1, p2⟩ := pi_bounds
  obtain ⟨a1, a2⟩ := abs_le.1 ham'
  obtain ⟨r1, r2⟩ := abs_le.1 her
  obtain ⟨w1, w2⟩ := abs_le.1 hωb
  obtain ⟨d1, d2⟩ := abs_le.1 hdvb
  obtain ⟨m1, m2⟩ := abs_le.1 hvm'
  obtain ⟨hk, _, hld⟩ := yaw_gain ham' hj hal hal'
  have hpl := A32.lo hpe
  have hph := A32.hi hpe
  have hkl := A32.lo hk
  have hkh := A32.hi hk
  have hll := A32.lo hld
  have hlh := A32.hi hld
  have b1 : is_negative_float al = false := isNeg_false hL hal (by rw [hal']; norm_num; linarith)
  have b2 : is_zero_float al = false :=
    isZero_false hal (by rw [hal', abs_of_pos (by linarith)]; norm_num; linarith)
  have b3 : is_zero_float (j / al) = false :=
    isZero_false hk.1 (by rw [abs_of_pos (by linarith)]; norm_num; linarith)
  have b4 : is_positive_float dt = true := isPos_true hdt (by rw [hdt']; norm_num)
  have b5 : is_positive_float al = true := isPos_true hal (by rw [hal']; norm_num; linarith)
  have b6 : is_positive_float (j / al) = true := isPos_true hk.1 (by norm_num; linarith)
  have c5 : ¬ pe > al / sq_float (j / al) := by
    rw [gt_iff_lt, Float32.lt_iff_toReal_lt hld.1 hpe.1]; linarith
  have c6 : ¬ pe < -(al / sq_float (j / al)) := by
    rw [Float32.lt_iff_toReal_lt hpe.1 ((Float32.isFinite_neg _).2 hld.1), Float32.toReal_neg]
    linarith
  have hV0e : sqrt_controller_float4 pe (j / al) al dt = pe * (j / al) := by
    rw [sc_eq_lin b1 b2 b3 b4 c5 c6]
    exact sqrtc_clamp_lin _ hpe.1 (by rw [abs_le]; constructor <;> linarith) hk.1 (by linarith)
      (by linarith) hdt (by rw [hdt']; norm_num) (by rw [hdt']; norm_num)
  have hV0 := A32.mul_c hpe hk (Ra := 29 / 10000) (Rb := 40)
    (by rw [abs_le]; constructor <;> linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [capF]) (e := 57 / 10 ^ 6) (by norm_num)
  have hvc := A32.sub_c (A32.of_exact hω) (A32.of_exact hdv) (R := 6)
    (by rw [abs_le]; constructor <;> linarith) (by norm_num [capF]) (e := 4 / 10 ^ 7) (by norm_num)
  have hP := A32.mul_c hV0 hvc (Ra := 116 / 1000) (Rb := 6)
    (by rw [abs_le]; constructor <;> linarith) (by rw [abs_le]; constructor <;> linarith)
    (by norm_num) (by norm_num) (by norm_num [capF]) (e := 35 / 10 ^ 5) (by norm_num)
  have hPl := A32.lo hP
  have hPh := A32.hi hP
  simp only [tgtYaw]
  rw [hV0e]
  have hle : Float32.abs pe ≤ al / sq_float (j / al) := by
    rw [Float32.le_iff_toReal_le ((Float32.isFinite_abs pe).2 hpe.1) hld.1, Float32.toReal_abs,
      abs_le]
    constructor <;> linarith
  have hacc : A32 (sqrt_controller_accel pe (pe * (j / al)) (ω - dv) (j / al) al / (j / al))
      (-(sgn01 (is_positive_float (pe * (j / al) * (ω - dv))) * (ω.toReal - dv.toReal)))
      (5 / 10 ^ 6) := by
    cases hσ : is_positive_float (pe * (j / al) * (ω - dv))
    · rw [sca_eq_zero hσ]
      obtain ⟨zf0, zv⟩ := zf hL
      have := A32.div_c (A32.of_val zf0 zv) hk (Ra := 0) (m := 3999 / 100) (Q := 0) (by simp)
        (by norm_num) (by rw [abs_of_pos (by norm_num : (0:ℝ) < 40)]; norm_num) (by norm_num)
        (by simp) (by norm_num [capF]) (e := 5 / 10 ^ 6) (by norm_num)
      exact this.congr (by simp [sgn01])
    · rw [sca_eq_lin hσ b5 b6 hle]
      have hnk := A32.mul_c (A32.neg hk) hvc (Ra := 40) (Rb := 6) (by norm_num)
        (by rw [abs_le]; constructor <;> linarith) (by norm_num) (by norm_num) (by norm_num [capF])
        (e := 10 / 10 ^ 5) (by norm_num)
      have hwd : |ω.toReal - dv.toReal| ≤ 6 := by rw [abs_le]; constructor <;> linarith
      have := A32.div_c hnk hk (Ra := 240) (m := 3999 / 100) (Q := 601 / 100)
        (by rw [abs_mul, abs_neg]; norm_num; linarith) (by norm_num)
        (by rw [abs_of_pos (by norm_num : (0:ℝ) < 40)]; norm_num) (by norm_num)
        (by rw [abs_div, abs_mul, abs_neg, abs_of_pos (by norm_num : (0:ℝ) < 40)]; norm_num
            linarith) (by norm_num [capF])
        (e := 5 / 10 ^ 6) (by norm_num)
      exact this.congr (by simp [sgn01]; ring)
  have hs0 := sgn01_nonneg (is_positive_float (pe * (j / al) * (ω - dv)))
  have hs1 := sgn01_le (is_positive_float (pe * (j / al) * (ω - dv)))
  refine ⟨is_positive_float (pe * (j / al) * (ω - dv)), ?_, ?_, ?_⟩
  · intro h
    have h' := (isPos_iff hP.1).1 h
    by_contra hc
    exact absurd (lt_of_le_of_lt h' (lt_of_le_of_lt hPh (by linarith))) (lt_irrefl _)
  · intro h
    have h' := not_le.1 ((isPos_iff hP.1).not.1 (by rw [h]; simp))
    by_contra hc
    exact absurd (lt_of_lt_of_le h' (le_trans (by linarith) hPl)) (lt_irrefl _)
  unfold yawCmd
  generalize sgn01 (is_positive_float (pe * (j / al) * (ω - dv))) = sg at hacc hs0 hs1 ⊢
  generalize sqrt_controller_accel pe (pe * (j / al)) (ω - dv) (j / al) al / (j / al) = Q at hacc ⊢
  have hsw : |sg * (ω.toReal - dv.toReal)| ≤ 6 := by
    rw [abs_mul, abs_of_nonneg hs0]
    have : |ω.toReal - dv.toReal| ≤ 6 := by rw [abs_le]; constructor <;> linarith
    nlinarith [abs_nonneg (ω.toReal - dv.toReal)]
  obtain ⟨q1, q2⟩ := abs_le.1 hsw
  have hV1 := A32.add_c hV0 hacc (R := 612 / 100) (by
    rw [abs_le]; constructor <;> linarith) (by norm_num [capF]) (e := 63 / 10 ^ 6) (by norm_num)
  have hvmA : A32 vm (Real.pi / 3) (1 / 10 ^ 6) := ⟨hvm, hvm'⟩
  have hnvm := A32.neg hvmA
  have hvlh : (-vm).toReal ≤ vm.toReal := by rw [Float32.toReal_neg]; linarith [A32.lo hvmA]
  have hV2 := A32.minmax hV1 hnvm hvmA hvlh
  have hS := abs_clampR_le (L := Real.pi / 3)
    (x := er * 40 + -(sg * (ω.toReal - dv.toReal))) (by linarith)
  obtain ⟨s1, s2⟩ := abs_le.1 hS
  have hvt0 := A32.add_c (A32.of_exact hdv) hV2 (R := 305 / 100) (by
    rw [abs_le]; constructor <;> linarith) (by norm_num [capF]) (e := 66 / 10 ^ 6) (by norm_num)
  have hvt := A32.minmax hvt0 hnvm hvmA hvlh
  have hS2 := abs_clampR_le (L := Real.pi / 3)
    (x := dv.toReal + clampR (-(Real.pi / 3)) (Real.pi / 3) (er * 40 + -(sg * (ω.toReal - dv.toReal))))
    (by linarith)
  obtain ⟨t1, t2⟩ := abs_le.1 hS2
  have hd := A32.sub_c hvt (A32.of_exact hω) (R := 505 / 100) (by
    rw [abs_le]; constructor <;> linarith) (by norm_num [capF]) (e := 69 / 10 ^ 6) (by norm_num)
  have hX := A32.mul_c hd hk (Ra := 505 / 100) (Rb := 40) (by
    rw [abs_le]; constructor <;> linarith) (by norm_num) (by norm_num) (by norm_num)
    (by norm_num [capF]) (e := 29 / 10 ^ 4) (by norm_num)
  obtain ⟨hlo, hhi⟩ := am_bounds ham ham'
  have hlh' : (-am).toReal ≤ am.toReal := by rw [Float32.toReal_neg]; linarith
  have hT0 := A32.cvl (Int32.toUInt32 334) hX hlo hhi hlh'
  obtain ⟨hT1f, hT1v⟩ := Float32.add_zero_val hT0.1 had had0
  have hT1 := A32.congr_x hT0 hT1f hT1v
  have hT := A32.cvl (Int32.toUInt32 341) hT1 hlo hhi hlh'
  rw [clampR_idem (by linarith)] at hT
  refine (hT.congr (by ring_nf)).mono (by norm_num)

/-- **(d) The yaw law in the linear zone.** For the yaw call (`max_ang_vel = slew` within `10⁻⁶`
of `π/3 = radians(60)`, `accel_max` within `10⁻⁵` of `3π/2 = radians(270)`,
`input_tc = _rate_y_tc = 0` (so `dt·10` is used), `dt = 1/400`), a heading error
`|e| ≤ 0.0029` (inside the linear distance `3π/3200 ≈ 0.002945`), a desired rate `|ψ̇| ≤ 2`,
`|ω| ≤ 4`, `|α| ≤ 32`: with `limit_total` both velocity clamps act,

  `α' ≈ α + clamp(clamp(40 (clamp(ψ̇ + clamp(40 e − σ (ω − ψ̇), ±π/3), ±π/3) − ω), ±3π/2) − α, ±3π/20)`
  within `β = 3.2·10⁻³`, and `ω' ≈ ω + α'/400` within `10⁻⁵`,

`σ` agreeing with the real product `40 e (ω − ψ̇) ≥ 2⁻²³` up to `3.5·10⁻⁴`. (For the rate-only
calls `e = (float) 0`, so `σ = false` and `α* = 40 (clamp(ψ̇, ±π/3) − ω)`.) -/
theorem yaw_law_linear (hL : LibmSpec) (e dv ω α vm am tc dt : Float32)
    (he : e.IsFinite) (heb : |e.toReal| ≤ 29 / 10000)
    (hdv : dv.IsFinite) (hdvb : |dv.toReal| ≤ 2) (hω : ω.IsFinite) (hωb : |ω.toReal| ≤ 4)
    (hα : α.IsFinite) (hαb : |α.toReal| ≤ 32)
    (hvm : vm.IsFinite) (hvm' : |vm.toReal - Real.pi / 3| ≤ 1 / 10 ^ 6)
    (ham : am.IsFinite) (ham' : |am.toReal - 3 * Real.pi / 2| ≤ 1 / 10 ^ 5)
    (htc : tc.IsFinite) (htc0 : tc.toReal = 0) (hdt : dt.IsFinite) (hdt' : dt.toReal = dtv) :
    ∃ σ : Bool,
      (σ = true → 2 ^ (-23 : ℤ) - 35 / 10 ^ 5 ≤ 40 * e.toReal * (ω.toReal - dv.toReal)) ∧
      (σ = false → 40 * e.toReal * (ω.toReal - dv.toReal) < 2 ^ (-23 : ℤ) + 35 / 10 ^ 5) ∧
      A32 (AC_AttitudeControl_Multi.attitude_command_model e dv ω α vm am tc dt).2
        (yawStep (yawCmd σ e.toReal dv.toReal ω.toReal) α.toReal) (32 / 10 ^ 4) ∧
      A32 (AC_AttitudeControl_Multi.attitude_command_model e dv ω α vm am tc dt).1
        (ω.toReal + yawStep (yawCmd σ e.toReal dv.toReal ω.toReal) α.toReal / 400) (1 / 10 ^ 5) := by
  obtain ⟨p1, p2⟩ := pi_bounds
  obtain ⟨a1, a2⟩ := abs_le.1 ham'
  obtain ⟨v1, v2⟩ := abs_le.1 hvm'
  obtain ⟨_, hj, hhi, hlo⟩ := yaw_consts hL ham ham' hdt hdt'
  have hdtp : is_positive_float dt = true := isPos_true hdt (by rw [hdt']; norm_num)
  have hamp : is_positive_float am = true := isPos_true ham (by norm_num; linarith)
  have htcp : is_positive_float tc = false := isPos_false htc (by rw [htc0]; norm_num)
  have hjp : is_positive_float (am / (dt * Float.toFloat32 (10.0 : Float))) = true :=
    isPos_true hj.1 (by have := A32.lo hj; norm_num [dtv] at this ⊢; linarith)
  have hnam : (-am).IsFinite := (Float32.isFinite_neg am).2 ham
  have hnvm : (-vm).IsFinite := (Float32.isFinite_neg vm).2 hvm
  have h1 : is_positive_float (-vm) = false :=
    isPos_false hnvm (by rw [Float32.toReal_neg]; norm_num; linarith)
  have h2 : is_negative_float vm = false := isNeg_false hL hvm (by norm_num; linarith)
  have h3 : is_negative_float (-am) = true := isNeg_true hL hnam (by
    rw [Float32.toReal_neg]; norm_num; linarith)
  have h6 : is_negative_float (-vm) = true := isNeg_true hL hnvm (by
    rw [Float32.toReal_neg]; norm_num; linarith)
  have h7 : is_positive_float vm = true := isPos_true hvm (by norm_num; linarith)
  simp only [AC_AttitudeControl_Multi.attitude_command_model, Id.run, hdtp, hamp, htcp,
    Bool.not_true, Bool.not_false, Bool.false_eq_true, ite_false, ite_true, id_pure_eq,
    shape_angle_vel_accel]
  rw [spva_yaw h1 h2 h3 hamp hjp h6 h7]
  obtain ⟨hpe, _⟩ := posErr_near hL he (by linarith)
  generalize Float.toFloat32 (Float32.toFloat (Float.toFloat32 (0.0 : Float) +
      wrap_PI_float (e - Float.toFloat32 (0.0 : Float))) -
      Float32.toFloat (Float.toFloat32 (0.0 : Float))) = pe at hpe ⊢
  have hal : (if is_positive_float pe = true then - -am else am).IsFinite ∧
      (if is_positive_float pe = true then - -am else am).toReal = am.toReal := by
    split
    · exact ⟨(Float32.isFinite_neg _).2 hnam, by rw [Float32.toReal_neg, Float32.toReal_neg, neg_neg]⟩
    · exact ⟨ham, rfl⟩
  generalize (if is_positive_float pe = true then - -am else am) = al at hal ⊢
  obtain ⟨hzf, hz0⟩ := zf hL
  obtain ⟨σ, hσ1, hσ2, hT⟩ := tgtYaw_lin hL hpe heb hdv hdvb hzf hz0 hω hωb hvm hvm' ham ham' hj
    hal.1 hal.2 hdt hdt'
  have hlh : (-(am / (dt * Float.toFloat32 (10.0 : Float))) * dt).toReal ≤
      (am / (dt * Float.toFloat32 (10.0 : Float)) * dt).toReal := by
    have := A32.hi hlo; have := A32.lo hhi; linarith
  have hcl := abs_clampR_le (L := 3 * Real.pi / 2) (x := yawCmd σ e.toReal dv.toReal ω.toReal)
    (by linarith)
  have hS := shape_accel_law hjp hdtp hT hα hαb (by linarith) hlo hhi hlh (by linarith)
    (by linarith) (by norm_num) (by norm_num)
  have hS' : A32 (shape_accel (tgtYaw pe dv (Float.toFloat32 0.0) ω (-vm) vm (-am) am
      (am / (dt * Float.toFloat32 (10.0 : Float))) al dt) α
      (am / (dt * Float.toFloat32 (10.0 : Float))) dt)
      (yawStep (yawCmd σ e.toReal dv.toReal ω.toReal) α.toReal) (32 / 10 ^ 4) :=
    (hS.congr (by simp only [yawStep])).mono (by norm_num)
  have hlaw : |yawStep (yawCmd σ e.toReal dv.toReal ω.toReal) α.toReal| ≤ 34 := by
    unfold yawStep
    have := abs_clampR_le (L := 3 * Real.pi / 20)
      (x := clampR (-(3 * Real.pi / 2)) (3 * Real.pi / 2) (yawCmd σ e.toReal dv.toReal ω.toReal) -
        α.toReal) (by linarith)
    have := abs_add_le α.toReal (clampR (-(3 * Real.pi / 20)) (3 * Real.pi / 20)
      (clampR (-(3 * Real.pi / 2)) (3 * Real.pi / 2) (yawCmd σ e.toReal dv.toReal ω.toReal) -
        α.toReal))
    linarith
  exact ⟨σ, hσ1, hσ2, hS', (omega_step hω (by linarith) hS' (by norm_num) hlaw hdt hdt').mono
    (by norm_num)⟩

/-! ## The target rate `ω' = ω + α'·dt` -/

/-- `attitude_command_model` returns `(ω + α'·dt, α')` (for `dt` positive). -/
theorem acm_fst {e dv ω α vm am tc dt : Float32} (hd : is_positive_float dt = true) :
    (AC_AttitudeControl_Multi.attitude_command_model e dv ω α vm am tc dt).1 =
      ω + (AC_AttitudeControl_Multi.attitude_command_model e dv ω α vm am tc dt).2 * dt := by
  simp only [AC_AttitudeControl_Multi.attitude_command_model, Id.run, hd, Bool.not_true,
    Bool.false_eq_true, ite_false, id_pure_eq]
  split_ifs <;> rfl

/-- **The target rate step** (with (c)): whenever the new acceleration `α'` is finite with
`|α'| ≤ 40`, and `|ω| ≤ 1000`, the new target rate is `ω + α'/400` up to `10⁻⁴` (the rounding of
`ω + α'·dt`, relative to `|ω|`); in particular `|ω' − ω| ≤ |α'|/400 + 10⁻⁴`. `ω'` itself is not
clamped. -/
theorem acm_rate_step {e dv ω α vm am tc dt : Float32} (hdt : dt.IsFinite) (hdt' : dt.toReal = dtv)
    (hω : ω.IsFinite) (hωb : |ω.toReal| ≤ 1000)
    (ha : (AC_AttitudeControl_Multi.attitude_command_model e dv ω α vm am tc dt).2.IsFinite)
    (hab : |(AC_AttitudeControl_Multi.attitude_command_model e dv ω α vm am tc dt).2.toReal| ≤ 40) :
    A32 (AC_AttitudeControl_Multi.attitude_command_model e dv ω α vm am tc dt).1
      (ω.toReal + (AC_AttitudeControl_Multi.attitude_command_model e dv ω α vm am tc dt).2.toReal / 400)
      (1 / 10 ^ 4) := by
  rw [acm_fst (isPos_true hdt (by rw [hdt']; norm_num))]
  generalize (AC_AttitudeControl_Multi.attitude_command_model e dv ω α vm am tc dt).2 = a at ha hab ⊢
  have hm := A32.mul_c (A32.of_exact ha) (A32.of_val hdt hdt') (Ra := 40) (Rb := 1 / 400) hab
    (by norm_num [dtv]) le_rfl le_rfl (by norm_num [capF]) (e := 1 / 10 ^ 8) (by norm_num)
  have hm' := A32.recenter hm (r' := a.toReal / 400) (d := 1 / 10 ^ 8) (by
    rw [show a.toReal * dtv - a.toReal / 400 = a.toReal * (dtv - 1 / 400) by ring, abs_mul]
    calc |a.toReal| * |dtv - 1 / 400| ≤ 40 * |dtv - 1 / 400| := by gcongr
      _ ≤ 1 / 10 ^ 8 := by norm_num [dtv])
  exact A32.add_c (A32.of_exact hω) hm' (R := 10002 / 10) (by
    have := abs_add_le ω.toReal (a.toReal / 400)
    rw [abs_div, abs_of_pos (by norm_num : (0:ℝ) < 400)] at this
    linarith) (by norm_num [capF]) (by norm_num)

/-! ## The parameter values -/

theorem radians_1800 (hL : LibmSpec) {d : Float32} (hd : d.IsFinite) (hD : d.toReal = 1800) :
    (radians_float d).IsFinite ∧ |(radians_float d).toReal - 10 * Real.pi| ≤ 1 / 10 ^ 5 := by
  have h := radians_near hL hd hD (by norm_num) (by norm_num)
  exact ⟨h.1, by have := h.2; rw [show (1800 : ℝ) * Real.pi / 180 = 10 * Real.pi by ring] at this
                 linarith [show (1800 : ℝ) * (4 / 10 ^ 9) + 1 / 10 ^ 39 ≤ 1 / 10 ^ 5 by norm_num]⟩

theorem radians_270 (hL : LibmSpec) {d : Float32} (hd : d.IsFinite) (hD : d.toReal = 270) :
    (radians_float d).IsFinite ∧ |(radians_float d).toReal - 3 * Real.pi / 2| ≤ 1 / 10 ^ 5 := by
  have h := radians_near hL hd hD (by norm_num) (by norm_num)
  exact ⟨h.1, by have := h.2; rw [show (270 : ℝ) * Real.pi / 180 = 3 * Real.pi / 2 by ring] at this
                 linarith [show (270 : ℝ) * (4 / 10 ^ 9) + 1 / 10 ^ 39 ≤ 1 / 10 ^ 5 by norm_num]⟩

theorem radians_60 (hL : LibmSpec) {d : Float32} (hd : d.IsFinite) (hD : d.toReal = 60) :
    (radians_float d).IsFinite ∧ |(radians_float d).toReal - Real.pi / 3| ≤ 1 / 10 ^ 6 := by
  have h := radians_near hL hd hD (by norm_num) (by norm_num)
  exact ⟨h.1, by have := h.2; rw [show (60 : ℝ) * Real.pi / 180 = Real.pi / 3 by ring] at this
                 linarith [show (60 : ℝ) * (4 / 10 ^ 9) + 1 / 10 ^ 39 ≤ 1 / 10 ^ 6 by norm_num]⟩

/-- `radians(0) = 0` (`ATC_RATE_R_MAX = ATC_RATE_P_MAX = 0`). -/
theorem radians_0 (hL : LibmSpec) {d : Float32} (hd : d.IsFinite) (hD : d.toReal = 0) :
    (radians_float d).IsFinite ∧ (radians_float d).toReal = 0 := by
  have hp := pi32 hL
  obtain ⟨pb1, pb2⟩ := piD_bounds
  have hη := η32_small
  have hη0 := η32_pos
  have hpe : u32 * piD + η32 ≤ 19 / 10 ^ 8 := by simp only [u32]; norm_num; nlinarith
  have hP := hp.mono hpe
  have Pl := A32.lo hP
  have Ph := A32.hi hP
  simp only [radians_float, id_run_eq, id_pure_eq]
  have hq' : (Float.toFloat32 (3.1415926535897931 : Float) / (180.0 : Float32)).IsFinite := by
    refine (Float32.div_err_all hp.1 f32_isFinite_180p0 (by rw [f32_toReal_180p0]; norm_num) ?_).1
    rw [f32_toReal_180p0, abs_div, abs_of_pos (by linarith), abs_of_pos (by norm_num : (0:ℝ) < 180)]
    have := Float32.one_le_maxFinite32
    rw [div_le_iff₀ (by norm_num)]; nlinarith
  obtain ⟨f, v⟩ := Float32.mul_exact hd hq' hd (by rw [hD, zero_mul])
  exact ⟨f, by rw [v, hD]⟩

theorem tc_005 : (0.05 : Float32).toReal = tcv := f32_toReal_0p05

end

end Contracts.Track.Att
