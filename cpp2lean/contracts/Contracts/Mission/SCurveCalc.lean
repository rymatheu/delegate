import Contracts.Mission.SCurvePathFloat

/-!
# What `SCurve::calculate_path` returns on the mission's ranges

`calcPath_spec`: for the snap, jerk, acceleration and speed limits of the mission's legs and a
half leg `L ≤ 1.81 m`, `calculate_path` returns finite outputs whose accelerating phase (with the
durations `add_segments` gives them) covers at most `L (1 + 1/1000)`. Per branch: the zero
returns, the short branch (`A`, ramp time from `powf`), and the long branch (`B`, `t₄` from the
quadratic root, `p7_t4_bound`); the cubic branch is excluded on these ranges.
-/

namespace Contracts.Mission

open Float.Model UnpackedFloat AC_WPNav_lib

noncomputable section

/-- The duration a segment actually gets in `add_segments` (`is_positive` gates it). -/
def eff (x : ℝ) : ℝ := by classical exact if 1 / 2 ^ 23 ≤ x then x else 0

/-- **What `calculate_path` returns** on the mission's ranges (half leg `L ≥ 10⁻⁴`): finite
outputs with `t₆ = t₂`, positive jerk and ramp time, `t₂` above `-FLT_EPSILON` (the final check)
and at most `1/2`, `0 ≤ t₄ ≤ 3`, maximum acceleration `A = J (t_j + t₂) ≤ 2`, and an accelerating
phase (with the durations `add_segments` gives the segments, `eff`) within `L (1 + 1/1000)`, which
either covers nearly `L` or ends at speed at least `1/4`. -/
structure CPOk (L : ℝ) (o : Float32 × Float32 × Float32 × Float32 × Float32) : Prop where
  fJ : o.1.IsFinite
  ftj : o.2.1.IsFinite
  ft2 : o.2.2.1.IsFinite
  ft4 : o.2.2.2.1.IsFinite
  t6 : o.2.2.2.2 = o.2.2.1
  J0 : 0 < o.1.toReal
  J1 : o.1.toReal ≤ 6
  tj0 : 1 / 300 ≤ o.2.1.toReal
  tj1 : o.2.1.toReal ≤ 1 / 4
  t20 : -(1 / 2 ^ 23) < o.2.2.1.toReal
  t21 : o.2.2.1.toReal ≤ 1 / 2
  t40 : 0 ≤ o.2.2.2.1.toReal
  t41 : o.2.2.2.1.toReal ≤ 3
  A : o.1.toReal * (o.2.1.toReal + eff o.2.2.1.toReal) ≤ 2
  p7 : SC.p7 (o.1.toReal * (o.2.1.toReal + eff o.2.2.1.toReal)) (2 * o.2.1.toReal + eff o.2.2.1.toReal)
    (eff o.2.2.2.1.toReal) ≤ L * (1 + 1 / 1000)
  low : L * (1 - 1 / 10 ^ 4) ≤ SC.p7 (o.1.toReal * (o.2.1.toReal + eff o.2.2.1.toReal))
      (2 * o.2.1.toReal + eff o.2.2.1.toReal) (eff o.2.2.2.1.toReal) ∨
    1 / 4 ≤ o.1.toReal * (o.2.1.toReal + eff o.2.2.1.toReal) *
      (2 * o.2.1.toReal + eff o.2.2.1.toReal + eff o.2.2.2.1.toReal)

theorem cpok_mk {L : ℝ} {J tj t2 t4 : Float32} (fJ : J.IsFinite) (ftj : tj.IsFinite)
    (ft2 : t2.IsFinite) (ft4 : t4.IsFinite) (J0 : 0 < J.toReal) (J1 : J.toReal ≤ 6)
    (tj0 : 1 / 300 ≤ tj.toReal) (tj1 : tj.toReal ≤ 1 / 4) (t20 : -(1 / 2 ^ 23) < t2.toReal)
    (t21 : t2.toReal ≤ 1 / 2) (t40 : 0 ≤ t4.toReal) (t41 : t4.toReal ≤ 3)
    (hA : J.toReal * (tj.toReal + eff t2.toReal) ≤ 2)
    (hp : SC.p7 (J.toReal * (tj.toReal + eff t2.toReal)) (2 * tj.toReal + eff t2.toReal)
      (eff t4.toReal) ≤ L * (1 + 1 / 1000))
    (hlow : L * (1 - 1 / 10 ^ 4) ≤ SC.p7 (J.toReal * (tj.toReal + eff t2.toReal))
        (2 * tj.toReal + eff t2.toReal) (eff t4.toReal) ∨
      1 / 4 ≤ J.toReal * (tj.toReal + eff t2.toReal) * (2 * tj.toReal + eff t2.toReal + eff t4.toReal)) :
    CPOk L (J, tj, t2, t4, t2) :=
  ⟨fJ, ftj, ft2, ft4, rfl, J0, J1, tj0, tj1, t20, t21, t40, t41, hA, hp, hlow⟩

theorem eff_nonneg (x : ℝ) : 0 ≤ eff x := by
  unfold eff; split_ifs with h
  · exact le_trans (by positivity) h
  · exact le_rfl

theorem eff_le {x : ℝ} (hx : 0 ≤ x) : eff x ≤ x := by
  unfold eff; split_ifs <;> linarith

theorem eff_zero : eff 0 = 0 := by
  unfold eff; split_ifs with h
  · norm_num at h
  · rfl

theorem eff_cases (x : ℝ) : (eff x = x ∧ 1 / 2 ^ 23 ≤ x) ∨ (eff x = 0 ∧ x < 1 / 2 ^ 23) := by
  unfold eff; split_ifs with h
  · exact Or.inl ⟨rfl, h⟩
  · exact Or.inr ⟨rfl, not_le.1 h⟩

theorem pos5 {a b c d e : Bool} (h : ¬(!a || !b || !c || !d || !e) = true) :
    a = true ∧ b = true ∧ c = true ∧ d = true ∧ e = true := by
  revert h; cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> decide

theorem fin10 {a b c d e a' b' c' d' e' : Bool}
    (h : ¬(!a || a' || !b || b' || !c || c' || !d || d' || !e || e') = true) :
    a = true ∧ a' = false ∧ b = true ∧ b' = false ∧ c = true ∧ c' = false ∧ d = true ∧ d' = false ∧
      e = true ∧ e' = false := by
  revert h; cases a <;> cases b <;> cases c <;> cases d <;> cases e <;> cases a' <;> cases b' <;>
    cases c' <;> cases d' <;> cases e' <;> decide

/-- The final check of `calculate_path` passed: finite outputs above `-FLT_EPSILON`. -/
theorem check_pass (hL : LibmSpec) {a b c d e : Float32}
    (h : ¬(!a.isFinite || is_negative_float a || !b.isFinite || is_negative_float b ||
      !c.isFinite || is_negative_float c || !d.isFinite || is_negative_float d ||
      !e.isFinite || is_negative_float e) = true) :
    a.IsFinite ∧ -(1 / 2 ^ 23) < a.toReal ∧ b.IsFinite ∧ -(1 / 2 ^ 23) < b.toReal ∧
      c.IsFinite ∧ -(1 / 2 ^ 23) < c.toReal ∧ d.IsFinite ∧ -(1 / 2 ^ 23) < d.toReal := by
  obtain ⟨fa, na, fb, nb, fc, nc, fd, nd, -, -⟩ := fin10 h
  have k : ∀ x : Float32, x.IsFinite → is_negative_float x = false → -(1 / 2 ^ 23) < x.toReal := by
    intro x hx hn
    by_contra hc
    have := (wp_isNeg_iff hL hx).2 (by
      have : (2 : ℝ) ^ (-23 : ℤ) = 1 / 2 ^ 23 := by norm_num
      rw [this]; linarith)
    rw [hn] at this; exact Bool.false_ne_true this
  exact ⟨fa, k a fa na, fb, k b fb nb, fc, k c fc nc, fd, k d fd nd⟩

/-- The final check of `calculate_path` does not fire on finite outputs above `-FLT_EPSILON`. -/
theorem check_fail (hL : LibmSpec) {a b c d e : Float32} (fa : a.IsFinite) (ha : -(1 / 2 ^ 23) < a.toReal)
    (fb : b.IsFinite) (hb : -(1 / 2 ^ 23) < b.toReal) (fc : c.IsFinite) (hc : -(1 / 2 ^ 23) < c.toReal)
    (fd : d.IsFinite) (hd : -(1 / 2 ^ 23) < d.toReal) (fe : e.IsFinite) (he : -(1 / 2 ^ 23) < e.toReal) :
    ¬(!a.isFinite || is_negative_float a || !b.isFinite || is_negative_float b ||
      !c.isFinite || is_negative_float c || !d.isFinite || is_negative_float d ||
      !e.isFinite || is_negative_float e) = true := by
  have k : ∀ x : Float32, x.IsFinite → -(1 / 2 ^ 23) < x.toReal → is_negative_float x = false := by
    intro x hx hn
    by_contra hc
    have := (wp_isNeg_iff hL hx).1 (by simpa using hc)
    rw [show (2 : ℝ) ^ (-23 : ℤ) = 1 / 2 ^ 23 by norm_num] at this; linarith
  have fa' : a.isFinite = true := fa
  have fb' : b.isFinite = true := fb
  have fc' : c.isFinite = true := fc
  have fd' : d.isFinite = true := fd
  have fe' : e.isFinite = true := fe
  rw [fa', fb', fc', fd', fe', k a fa ha, k b fb hb, k c fc hc, k d fd hd, k e fe he]
  decide

theorem cpok_check (hL : LibmSpec) {L : ℝ} {J tj t2 t4 : Float32} (h : CPOk L (J, tj, t2, t4, t2)) :
    ¬(!J.isFinite || is_negative_float J || !tj.isFinite || is_negative_float tj ||
      !t2.isFinite || is_negative_float t2 || !t4.isFinite || is_negative_float t4 ||
      !t2.isFinite || is_negative_float t2) = true :=
  check_fail hL h.fJ (by linarith [h.J0]) h.ftj (by linarith [h.tj0]) h.ft2 h.t20 h.ft4
    (by linarith [h.t40]) h.ft2 h.t20

theorem R32.mul_ex {a b : Float32} (fa : a.IsFinite) (fb : b.IsFinite)
    (hlo : (1 / 2 ^ 60 : ℝ) ≤ |a.toReal * b.toReal|) (hhi : |a.toReal * b.toReal| ≤ 2 ^ 90) :
    R32 (a * b) (a.toReal * b.toReal) 2 :=
  R32.mul (R32.of_exact fa (le_refl (0 : ℝ))) (R32.of_exact fb (le_refl (0 : ℝ))) le_rfl le_rfl
    (by norm_num) (by norm_num) hlo hhi (by norm_num)

/-- The two-sided form of `R32`. -/
theorem R32.bounds {x : Float32} {r k : ℝ} (h : R32 x r k) (hr : 0 < r) :
    r * (1 - k / 16777216) ≤ x.toReal ∧ x.toReal ≤ r * (1 + k / 16777216) := by
  have := h.2
  rw [abs_of_pos hr] at this
  obtain ⟨h1, h2⟩ := abs_le.1 this
  constructor <;> nlinarith

theorem pf_bounds {pf : Float32} (h : R32 pf Real.pi 2) :
    3141591 / 1000000 ≤ pf.toReal ∧ pf.toReal ≤ 3141594 / 1000000 := by
  have p1 := Real.pi_gt_d6
  have p2 := Real.pi_lt_d6
  have := h.bounds Real.pi_pos
  constructor <;> nlinarith

theorem f32_third : (1.0 : Float32) / (3.0 : Float32) = 0.333333343 := by decide +kernel

theorem f32_isZero_zero : is_zero_float (0.0 : Float32) = true := by decide +kernel

/-- `At = min (Am, Vm / (2 tj), L / (4 tj²))`: finite, at most `Am` and at most `7 L`. -/
theorem At_spec {Am Vm L T At : Float32} (fA : Am.IsFinite) (hA0 : 99 / 100 ≤ Am.toReal) (fV : Vm.IsFinite)
    (hV : 99 / 100 ≤ Vm.toReal ∧ Vm.toReal ≤ 271 / 100) (fL : L.IsFinite)
    (hL0 : 1 / 2 ^ 23 ≤ L.toReal) (hL1 : L.toReal ≤ 181 / 100) (fT : T.IsFinite)
    (hT : 19 / 100 ≤ T.toReal ∧ T.toReal ≤ 21 / 100)
    (hAt : MIN_float2 (MIN_float2 Am ((Vm - 0.0) / (2.0 * T)))
      ((L - 4.0 * 0.0 * T) / (4.0 * sq_float T)) = At) :
    At.IsFinite ∧ At.toReal ≤ Am.toReal ∧ At.toReal ≤ 7 * L.toReal ∧
      (1 / 10 ^ 4 ≤ L.toReal → 1 / 2 ^ 23 ≤ At.toReal) := by
  have e0 := f32_toReal_0p0
  have f0 := f32_isFinite_0p0
  obtain ⟨fVs, eVs⟩ := Float32.sub_zero_val fV f0 e0
  have m2 := R32.mul_ex f32_isFinite_2p0 fT
    (by rw [f32_toReal_2p0, abs_of_pos (by linarith)]; nlinarith)
    (by rw [f32_toReal_2p0, abs_of_pos (by linarith)]; nlinarith)
  rw [f32_toReal_2p0] at m2
  have d1 := R32.div (k := 4) (R32.of_exact fVs (le_refl (0 : ℝ))) m2 le_rfl (by norm_num)
    (by norm_num) (by norm_num) (ne_of_gt (by linarith))
    (by rw [eVs, abs_div, abs_of_pos (by linarith), abs_of_pos (by linarith),
          le_div_iff₀ (by linarith)]; nlinarith)
    (by rw [eVs, abs_div, abs_of_pos (by linarith), abs_of_pos (by linarith),
          div_le_iff₀ (by linarith)]; nlinarith)
    (by norm_num)
  obtain ⟨f40, e40⟩ := Float32.mul_zero_val f32_isFinite_4p0 f0 e0
  obtain ⟨f40T, e40T⟩ := Float32.mul_exact f40 fT f0 (by rw [e40, zero_mul, e0])
  rw [e0] at e40T
  obtain ⟨fLs, eLs⟩ := Float32.sub_zero_val fL f40T e40T
  have sq : sq_float T = T * T := rfl
  rw [sq] at hAt
  have mTT := R32.mul_ex fT fT (by rw [abs_of_pos (by nlinarith)]; nlinarith)
    (by rw [abs_of_pos (by nlinarith)]; nlinarith)
  have m4 := R32.mul (k := 4) (R32.of_exact f32_isFinite_4p0 (le_refl (0 : ℝ))) mTT le_rfl
    (by norm_num) (by norm_num) (by norm_num)
    (by rw [f32_toReal_4p0, abs_of_pos (by nlinarith)]; nlinarith)
    (by rw [f32_toReal_4p0, abs_of_pos (by nlinarith)]; nlinarith) (by norm_num)
  rw [f32_toReal_4p0] at m4
  have d2 := R32.div (k := 6) (R32.of_exact fLs (le_refl (0 : ℝ))) m4 le_rfl (by norm_num)
    (by norm_num) (by norm_num) (ne_of_gt (by nlinarith))
    (by rw [eLs, abs_div, abs_of_pos (by linarith), abs_of_pos (by nlinarith),
          le_div_iff₀ (by nlinarith)]; nlinarith)
    (by rw [eLs, abs_div, abs_of_pos (by linarith), abs_of_pos (by nlinarith),
          div_le_iff₀ (by nlinarith)]; nlinarith)
    (by norm_num)
  obtain ⟨fm1, em1⟩ := wp_min_spec fA d1.1
  obtain ⟨fm2, em2⟩ := wp_min_spec fm1 d2.1
  rw [hAt] at fm2 em2
  refine ⟨fm2, ?_, ?_, ?_⟩
  · rw [em2, em1]; exact (min_le_left _ _).trans (min_le_left _ _)
  · rw [em2]
    refine (min_le_right _ _).trans ?_
    have hq : 0 < L.toReal / (4 * (T.toReal * T.toReal)) := by
      have : 0 < L.toReal := lt_of_lt_of_le (by norm_num) hL0
      exact div_pos this (by nlinarith)
    have := (d2.bounds (by rw [eLs]; exact hq)).2
    rw [eLs] at this
    have h2 : L.toReal / (4 * (T.toReal * T.toReal)) ≤ L.toReal * (1 / (4 * (19 / 100) ^ 2)) := by
      rw [div_le_iff₀ (by nlinarith)]
      have : 0 ≤ L.toReal := le_trans (by norm_num) hL0
      have h3 : 4 * (19 / 100) ^ 2 ≤ 4 * (T.toReal * T.toReal) := by nlinarith
      calc L.toReal = L.toReal * (1 / (4 * (19 / 100) ^ 2)) * (4 * (19 / 100) ^ 2) := by field_simp
        _ ≤ _ := by gcongr
    have : 0 ≤ L.toReal := le_trans (by norm_num) hL0
    nlinarith
  · intro hL4
    rw [em2, em1]
    have q1 := (d1.bounds (by rw [eVs]; exact div_pos (by linarith) (by linarith))).1
    have q2 := (d2.bounds (by rw [eLs]; exact div_pos (by linarith) (by nlinarith))).1
    rw [eVs] at q1
    rw [eLs] at q2
    have r1 : 2 ≤ Vm.toReal / (2 * T.toReal) := by
      rw [le_div_iff₀ (by linarith)]; nlinarith
    have r2 : 1 / 2000 ≤ L.toReal / (4 * (T.toReal * T.toReal)) := by
      rw [le_div_iff₀ (by nlinarith)]; nlinarith
    refine le_min (le_min (by linarith) (by nlinarith)) (by nlinarith)


/-- `X π / (c Sm)` in `float` (the arguments of the short branch's `powf` and `sqrt`). -/
theorem arg_spec {X pf c Sm : Float32} (fX : X.IsFinite) (fc : c.IsFinite) (fS : Sm.IsFinite)
    (hpf : R32 pf Real.pi 2) (hX : 1 / 2 ^ 23 ≤ X.toReal ∧ X.toReal ≤ 4)
    (hc : 2 ≤ c.toReal ∧ c.toReal ≤ 8) (hS : 39 ≤ Sm.toReal ∧ Sm.toReal ≤ 40) :
    R32 (X * pf / (c * Sm)) (X.toReal * Real.pi / (c.toReal * Sm.toReal)) 8 := by
  have p1 := Real.pi_gt_d6
  have p2 := Real.pi_lt_d6
  have m1 := R32.mul (k := 4) (R32.of_exact fX (le_refl (0 : ℝ))) hpf le_rfl (by norm_num)
    (by norm_num) (by norm_num)
    (by rw [abs_of_pos (by nlinarith)]; nlinarith) (by rw [abs_of_pos (by nlinarith)]; nlinarith)
    (by norm_num)
  have m2 := R32.mul_ex fc fS (by rw [abs_of_pos (by nlinarith)]; nlinarith)
    (by rw [abs_of_pos (by nlinarith)]; nlinarith)
  have hX0 : 0 < X.toReal := lt_of_lt_of_le (by norm_num) hX.1
  have hcS : 78 ≤ c.toReal * Sm.toReal ∧ c.toReal * Sm.toReal ≤ 320 := ⟨by nlinarith, by nlinarith⟩
  exact R32.div m1 m2 (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (ne_of_gt (by linarith))
    (by rw [abs_div, abs_of_pos (by nlinarith), abs_of_pos (by linarith), le_div_iff₀ (by linarith)]
        nlinarith)
    (by rw [abs_div, abs_of_pos (by nlinarith), abs_of_pos (by linarith), div_le_iff₀ (by linarith)]
        nlinarith)
    (by norm_num)

theorem rpow_pow_eq {x q : ℝ} (hx : 0 ≤ x) (n : ℕ) : (x ^ q) ^ n = x ^ (q * n) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx]

set_option maxHeartbeats 4000000 in
/-- **The short branch's ramp time** `tA = min (tj, (L π/(8 Sm))^¼, (Vm π/(4 Sm))^⅓, √(Am π/(2 Sm)))`
and jerk `JA = 2 Sm tA / π`: the accelerating phase `4 JA tA³` is within `10⁻⁵` of `L` from above,
and at least `min (0.12, L (1 - 10⁻⁵))`. -/
theorem branchA_spec (hL : LibmSpec) {Sm Am Vm L pf T tA JA : Float32}
    (fS : Sm.IsFinite) (hS : 39 ≤ Sm.toReal ∧ Sm.toReal ≤ 40)
    (fA : Am.IsFinite) (hA : 99 / 100 ≤ Am.toReal ∧ Am.toReal ≤ 182 / 100)
    (fV : Vm.IsFinite) (hV : 99 / 100 ≤ Vm.toReal ∧ Vm.toReal ≤ 271 / 100)
    (fL : L.IsFinite) (hL0 : 1 / 2 ^ 23 ≤ L.toReal) (hL1 : L.toReal ≤ 181 / 100)
    (hpf : R32 pf Real.pi 2) (fT : T.IsFinite) (hT : 19 / 100 ≤ T.toReal ∧ T.toReal ≤ 21 / 100)
    (htA : MIN_float2 (MIN_float2 (MIN_float2 T ((L * pf / (8.0 * Sm)).pow (1.0 / 4.0)))
      ((Vm * pf / (4.0 * Sm)).pow (1.0 / 3.0))) (safe_sqrt_float (Am * pf / (2.0 * Sm))) = tA)
    (hJA : 2.0 * Sm * tA / pf = JA) :
    tA.IsFinite ∧ 1 / 300 ≤ tA.toReal ∧ tA.toReal ≤ 21 / 100 ∧ JA.IsFinite ∧
      24 * tA.toReal ≤ JA.toReal ∧ JA.toReal ≤ 26 * tA.toReal ∧
      4 * JA.toReal * tA.toReal ^ 3 ≤ L.toReal * (1 + 1 / 10 ^ 5) ∧
      min (12 / 100) (L.toReal * (1 - 1 / 10 ^ 5)) ≤ 4 * JA.toReal * tA.toReal ^ 3 := by
  have p1 := Real.pi_gt_d6
  have p2 := Real.pi_lt_d6
  have hπ := Real.pi_pos
  rw [f32_quarter, f32_third] at htA
  have hL0' : 0 < L.toReal := lt_of_lt_of_le (by norm_num) hL0
  -- the three candidates
  have a4 := arg_spec fL f32_isFinite_8p0 fS hpf ⟨hL0, by linarith⟩
    (by rw [f32_toReal_8p0]; norm_num) hS
  rw [f32_toReal_8p0] at a4
  set x4 := L.toReal * Real.pi / (8 * Sm.toReal) with hx4d
  have hx4 : 0 < x4 := div_pos (by positivity) (by linarith)
  have hx4lo : 1 / 2 ^ 32 ≤ x4 := by
    rw [hx4d, le_div_iff₀ (by linarith)]; nlinarith
  have P4 := R32.pow (k := 13) hL a4 f32_isFinite_0p25 (by rw [f32_toReal_0p25]; norm_num)
    (by rw [f32_toReal_0p25]; norm_num) (by norm_num) (by norm_num) hx4
    (by rw [hx4d, div_le_iff₀ (by linarith)]; nlinarith) (by norm_num)
  rw [f32_toReal_0p25] at P4
  set y := x4 ^ (1 / 4 : ℝ) with hyd
  have hy : 0 < y := Real.rpow_pos_of_pos hx4 _
  have hy4 : y ^ 4 = x4 := by
    rw [hyd, rpow_pow_eq hx4.le]; norm_num
  have hylo : 1 / 2 ^ 8 ≤ y := by
    by_contra hc
    have : y ^ 4 < (1 / 2 ^ 8) ^ 4 := pow_lt_pow_left₀ (not_le.1 hc) hy.le (by norm_num)
    rw [hy4] at this; norm_num at this; linarith
  obtain ⟨P4lo, P4hi⟩ := P4.bounds hy
  have a3 := arg_spec fV f32_isFinite_4p0 fS hpf ⟨by linarith, by linarith⟩
    (by rw [f32_toReal_4p0]; norm_num) hS
  rw [f32_toReal_4p0] at a3
  set x3 := Vm.toReal * Real.pi / (4 * Sm.toReal) with hx3d
  have hx3lo : 194 / 10000 ≤ x3 := by rw [hx3d, le_div_iff₀ (by linarith)]; nlinarith
  have hx3hi : x3 ≤ 1 := by rw [hx3d, div_le_iff₀ (by linarith)]; nlinarith
  have hx3 : 0 < x3 := by linarith
  have P3 := R32.pow (k := 13) hL a3 f32_isFinite_0p333333343
    (by rw [f32_toReal_0p333333343]; norm_num) (by rw [f32_toReal_0p333333343]; norm_num)
    (by norm_num) (by norm_num) hx3 (by linarith) (by norm_num)
  rw [f32_toReal_0p333333343] at P3
  have hz : (195 / 1000 : ℝ) ≤ x3 ^ (11184811 / 33554432 : ℝ) := by
    have h1 : x3 ^ (3 / 8 : ℝ) ≤ x3 ^ (11184811 / 33554432 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_ge hx3 hx3hi (by norm_num)
    have h2 : (195 / 1000 : ℝ) ≤ x3 ^ (3 / 8 : ℝ) := by
      by_contra hc
      have : (x3 ^ (3 / 8 : ℝ)) ^ 8 < (195 / 1000) ^ 8 :=
        pow_lt_pow_left₀ (not_le.1 hc) (Real.rpow_nonneg hx3.le _) (by norm_num)
      rw [rpow_pow_eq hx3.le] at this
      norm_num at this
      have h3 : (194 / 10000 : ℝ) ^ 3 ≤ x3 ^ 3 := pow_le_pow_left₀ (by norm_num) hx3lo 3
      norm_num at h3
      linarith
    linarith
  obtain ⟨P3lo, -⟩ := P3.bounds (by linarith)
  have aS := arg_spec fA f32_isFinite_2p0 fS hpf ⟨by linarith, by linarith⟩
    (by rw [f32_toReal_2p0]; norm_num) hS
  rw [f32_toReal_2p0] at aS
  set xS := Am.toReal * Real.pi / (2 * Sm.toReal) with hxSd
  have hxSlo : 388 / 10000 ≤ xS := by rw [hxSd, le_div_iff₀ (by linarith)]; nlinarith
  have hxShi : xS ≤ 1 := by rw [hxSd, div_le_iff₀ (by linarith)]; nlinarith
  obtain ⟨aSlo, -⟩ := aS.bounds (by linarith)
  rw [(wp_safe_sqrt hL aS.1).1 (by nlinarith)] at htA
  have SS := R32.sqrt (k := 10) aS (by norm_num) (by norm_num)
    (by linarith) (by linarith) (by norm_num)
  have hSlo : (195 / 1000 : ℝ) ≤ Real.sqrt xS := by
    rw [show (195 / 1000 : ℝ) = Real.sqrt ((195 / 1000) ^ 2) by
      rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  obtain ⟨Slo, -⟩ := SS.bounds (by linarith)
  -- `tA`
  obtain ⟨f1, e1⟩ := wp_min_spec fT P4.1
  obtain ⟨f2, e2⟩ := wp_min_spec f1 P3.1
  obtain ⟨f3, e3⟩ := wp_min_spec f2 SS.1
  rw [htA] at f3 e3
  have tle : tA.toReal ≤ T.toReal := by
    rw [e3, e2, e1]; exact (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_left _ _))
  have tleP : tA.toReal ≤ (Float32.pow (L * pf / (8.0 * Sm)) 0.25).toReal := by
    rw [e3, e2, e1]; exact (min_le_left _ _).trans ((min_le_left _ _).trans (min_le_right _ _))
  have tge : min (19 / 100) (Float32.pow (L * pf / (8.0 * Sm)) 0.25).toReal ≤ tA.toReal := by
    rw [e3, e2, e1]
    simp only [le_min_iff]
    refine ⟨⟨⟨min_le_iff.2 (Or.inl hT.1), min_le_right _ _⟩, min_le_iff.2 (Or.inl ?_)⟩,
      min_le_iff.2 (Or.inl ?_)⟩
    · have : (195 / 1000 : ℝ) * (1 - 13 / 16777216) ≤ x3 ^ (11184811 / 33554432 : ℝ) * (1 - 13 / 16777216) := by
        gcongr
      linarith
    · have : (195 / 1000 : ℝ) * (1 - 10 / 16777216) ≤ Real.sqrt xS * (1 - 10 / 16777216) := by
        gcongr
      linarith
  have hP4lo : 1 / 300 ≤ (Float32.pow (L * pf / (8.0 * Sm)) 0.25).toReal := by
    have : (1 / 2 ^ 8 : ℝ) * (1 - 13 / 16777216) ≤ y * (1 - 13 / 16777216) := by
      gcongr
    linarith
  have ht0 : 1 / 300 ≤ tA.toReal := le_trans (le_min (by norm_num) hP4lo) tge
  have htp : 0 < tA.toReal := by linarith
  -- `JA`
  have m2 := R32.two_mul (R32.of_exact fS (le_refl (0 : ℝ))) le_rfl (by norm_num)
    (by rw [abs_of_pos (by linarith)]; nlinarith) (by rw [abs_of_pos (by linarith)]; nlinarith)
  have m3 := R32.mul (k := 3) m2 (R32.of_exact f3 (le_refl (0 : ℝ))) (by norm_num) le_rfl
    (by norm_num) (by norm_num)
    (by rw [abs_of_pos (by nlinarith)]; nlinarith) (by rw [abs_of_pos (by nlinarith)]; nlinarith)
    (by norm_num)
  have dJ := R32.div (k := 7) m3 hpf (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    (ne_of_gt hπ)
    (by rw [abs_div, abs_of_pos (by nlinarith), abs_of_pos hπ, le_div_iff₀ hπ]; nlinarith)
    (by rw [abs_div, abs_of_pos (by nlinarith), abs_of_pos hπ, div_le_iff₀ hπ]; nlinarith)
    (by norm_num)
  rw [hJA] at dJ
  set J0 := 2 * Sm.toReal * tA.toReal / Real.pi with hJ0d
  have hS0 : 0 < Sm.toReal := by linarith
  have hJ0 : 0 < J0 := div_pos (by nlinarith) hπ
  obtain ⟨Jlo, Jhi⟩ := dJ.bounds hJ0
  have hJ0lo : 2482 / 100 * tA.toReal ≤ J0 := by
    rw [hJ0d, le_div_iff₀ hπ]; nlinarith [mul_le_mul_of_nonneg_right (le_of_lt p2) htp.le]
  have hJ0hi : J0 ≤ 2547 / 100 * tA.toReal := by
    rw [hJ0d, div_le_iff₀ hπ]; nlinarith [mul_le_mul_of_nonneg_right (le_of_lt p1) htp.le]
  have hK : 4 * J0 * tA.toReal ^ 3 = 8 * Sm.toReal / Real.pi * tA.toReal ^ 4 := by
    rw [hJ0d]; field_simp; ring
  have hx : 8 * Sm.toReal / Real.pi * x4 = L.toReal := by
    rw [hx4d]; field_simp [hS0.ne', hπ.ne']
  refine ⟨f3, ht0, by linarith, dJ.1, by nlinarith, by nlinarith, ?_, ?_⟩
  · have h4 : tA.toReal ^ 4 ≤ x4 * (1 + 13 / 16777216) ^ 4 := by
      rw [← hy4, ← mul_pow]
      exact pow_le_pow_left₀ htp.le (tleP.trans P4hi) 4
    have hc : 0 ≤ 8 * Sm.toReal / Real.pi := div_nonneg (by linarith) hπ.le
    calc 4 * JA.toReal * tA.toReal ^ 3 ≤ 4 * (J0 * (1 + 7 / 16777216)) * tA.toReal ^ 3 := by
          gcongr
      _ = 8 * Sm.toReal / Real.pi * tA.toReal ^ 4 * (1 + 7 / 16777216) := by rw [← hK]; ring
      _ ≤ 8 * Sm.toReal / Real.pi * (x4 * (1 + 13 / 16777216) ^ 4) * (1 + 7 / 16777216) := by
          gcongr
      _ = L.toReal * ((1 + 13 / 16777216) ^ 4 * (1 + 7 / 16777216)) := by rw [← hx]; ring
      _ ≤ L.toReal * (1 + 1 / 10 ^ 5) := by gcongr; norm_num
  · rcases le_total (19 / 100) (Float32.pow (L * pf / (8.0 * Sm)) 0.25).toReal with hc | hc
    · rw [min_eq_left hc] at tge
      apply min_le_of_left_le
      have h4 : (19 / 100 : ℝ) ^ 4 ≤ tA.toReal ^ 4 := pow_le_pow_left₀ (by norm_num) tge 4
      have : 24 * tA.toReal * tA.toReal ^ 3 ≤ JA.toReal * tA.toReal ^ 3 := by
        have : 24 * tA.toReal ≤ JA.toReal := by nlinarith
        gcongr
      nlinarith
    · rw [min_eq_right hc] at tge
      apply min_le_of_right_le
      have h4 : x4 * (1 - 13 / 16777216) ^ 4 ≤ tA.toReal ^ 4 := by
        rw [← hy4, ← mul_pow]
        exact pow_le_pow_left₀ (by nlinarith) (P4lo.trans tge) 4
      have hc' : 0 ≤ 8 * Sm.toReal / Real.pi := div_nonneg (by linarith) hπ.le
      calc L.toReal * (1 - 1 / 10 ^ 5) ≤ L.toReal * ((1 - 13 / 16777216) ^ 4 * (1 - 7 / 16777216)) := by
            gcongr; norm_num
        _ = 8 * Sm.toReal / Real.pi * (x4 * (1 - 13 / 16777216) ^ 4) * (1 - 7 / 16777216) := by
            rw [← hx]; ring
        _ ≤ 8 * Sm.toReal / Real.pi * tA.toReal ^ 4 * (1 - 7 / 16777216) := by gcongr
        _ = 4 * (J0 * (1 - 7 / 16777216)) * tA.toReal ^ 3 := by rw [← hK]; ring
        _ ≤ 4 * JA.toReal * tA.toReal ^ 3 := by gcongr


theorem p7_expand (A R t : ℝ) : SC.p7 A R t = A * R ^ 2 + 3 / 2 * A * R * t + A * t ^ 2 / 2 := by
  simp only [SC.p7]; ring

theorem p7_scale {A R t c : ℝ} (hA : 0 ≤ A) (hR : 0 ≤ R) (ht : 0 ≤ t) (hc : 1 ≤ c) :
    SC.p7 (A * c) (R * c) t ≤ c ^ 3 * SC.p7 A R t := by
  simp only [SC.p7]
  have h1 : R * c + t ≤ c * (R + t) := by nlinarith
  have h2 : 2 * (R * c) + t ≤ c * (2 * R + t) := by nlinarith
  have h3 : (R * c + t) * (2 * (R * c) + t) ≤ (c * (R + t)) * (c * (2 * R + t)) :=
    mul_le_mul h1 h2 (by positivity) (by positivity)
  have h4 : A * c * ((R * c + t) * (2 * (R * c) + t)) ≤ A * c * ((c * (R + t)) * (c * (2 * R + t))) :=
    mul_le_mul_of_nonneg_left h3 (by positivity)
  have e1 : A * c * (R * c + t) * (2 * (R * c) + t) / 2 = A * c * ((R * c + t) * (2 * (R * c) + t)) / 2 := by ring
  have e2 : c ^ 3 * (A * (R + t) * (2 * R + t) / 2) = A * c * ((c * (R + t)) * (c * (2 * R + t))) / 2 := by ring
  rw [e1, e2]; linarith

/-- A constant-acceleration time within the bound on the accelerating phase is at most `3 s`. -/
theorem t4_le_three {A R t L : ℝ} (hA : 0 < A) (hR : 0 < R) (hR1 : R ≤ 1) (ht : 0 ≤ t)
    (hp : SC.p7 A R t ≤ L * (1 + 1 / 2000)) (hL : L ≤ 2)
    (hc : 1 / 2 ≤ A ∨ L * (1 - 1 / 10 ^ 4) ≤ A * R ^ 2) : t ≤ 3 := by
  rw [p7_expand] at hp
  by_contra h
  have h := not_le.1 h
  have hAR : 0 < A * R := mul_pos hA hR
  have hAR2 : 0 < A * R ^ 2 := by positivity
  have hART : 0 ≤ A * R * t := by positivity
  rcases hc with hc | hc
  · have : 9 < t ^ 2 := by nlinarith
    have : 9 / 2 < A * t ^ 2 := by nlinarith
    nlinarith
  · have : 9 / 2 * (A * R) < 3 / 2 * A * R * t := by nlinarith
    have : A * R ^ 2 ≤ A * R := by nlinarith
    have : 0 ≤ A * t ^ 2 := by positivity
    nlinarith

set_option maxHeartbeats 4000000 in
/-- **The short branch's outputs**: the result with `t₄ = 0` and the one with the quadratic `t₄`
both satisfy `CPOk`. -/
theorem branchA_ok (hL : LibmSpec) {L Vm tA JA : Float32} (fL : L.IsFinite)
    (hL0 : 1 / 2 ^ 23 ≤ L.toReal) (hL1 : L.toReal ≤ 181 / 100) (fV : Vm.IsFinite)
    (hV : 99 / 100 ≤ Vm.toReal ∧ Vm.toReal ≤ 271 / 100) (ftA : tA.IsFinite)
    (ht0 : 1 / 300 ≤ tA.toReal) (ht1 : tA.toReal ≤ 21 / 100) (fJA : JA.IsFinite)
    (hJ1 : 24 * tA.toReal ≤ JA.toReal) (hJ2 : JA.toReal ≤ 26 * tA.toReal)
    (hK1 : 4 * JA.toReal * tA.toReal ^ 3 ≤ L.toReal * (1 + 1 / 10 ^ 5))
    (hK2 : min (12 / 100) (L.toReal * (1 - 1 / 10 ^ 5)) ≤ 4 * JA.toReal * tA.toReal ^ 3) :
    CPOk L.toReal (JA, tA, (0.0 : Float32), (0.0 : Float32), (0.0 : Float32)) ∧
      CPOk L.toReal (JA, tA, (0.0 : Float32), t4F (JA * tA) JA tA L Vm, (0.0 : Float32)) := by
  have hL0' : 0 < L.toReal := lt_of_lt_of_le (by norm_num) hL0
  have htp : 0 < tA.toReal := by linarith
  have hJp : 0 < JA.toReal := by nlinarith
  have hp0 : SC.p7 (JA.toReal * tA.toReal) (2 * tA.toReal) 0 = 4 * JA.toReal * tA.toReal ^ 3 := by
    simp only [SC.p7]; ring
  have e0 : (0.0 : Float32).toReal = 0 := f32_toReal_0p0
  have hA' : JA.toReal * (tA.toReal + eff (0.0 : Float32).toReal) ≤ 2 := by
    rw [e0, eff_zero, add_zero]; nlinarith
  have hlow0 : 12 / 100 ≤ 4 * JA.toReal * tA.toReal ^ 3 →
      1 / 4 ≤ JA.toReal * tA.toReal * (2 * tA.toReal) := by
    intro h; nlinarith
  constructor
  · refine cpok_mk fJA ftA f32_isFinite_0p0 f32_isFinite_0p0 hJp (by nlinarith) ht0 (by linarith)
      (by rw [e0]; norm_num) (by rw [e0]; norm_num) (by rw [e0]) (by rw [e0]; norm_num) hA' ?_ ?_
    · rw [e0, eff_zero, add_zero, add_zero, hp0]
      calc _ ≤ L.toReal * (1 + 1 / 10 ^ 5) := hK1
        _ ≤ L.toReal * (1 + 1 / 1000) := by gcongr; norm_num
    · rw [e0, eff_zero, add_zero, add_zero, add_zero, hp0]
      rcases min_choice (12 / 100 : ℝ) (L.toReal * (1 - 1 / 10 ^ 5)) with hm | hm <;> rw [hm] at hK2
      · exact Or.inr (hlow0 hK2)
      · left; nlinarith
  -- `Am = JA tA` in `float`
  have mA := R32.mul_ex fJA ftA (by rw [abs_of_pos (by positivity)]; nlinarith)
    (by rw [abs_of_pos (by positivity)]; nlinarith)
  obtain ⟨alo, ahi⟩ := mA.bounds (by positivity)
  set a := (JA * tA).toReal with had
  set j := JA.toReal
  set t := tA.toReal
  have hjt : 24 / 90000 ≤ j * t := by nlinarith
  have hjt' : j * t ≤ 26 * (21 / 100) ^ 2 := by nlinarith
  have ha0 : 0 < a := by nlinarith
  have hQ : QIn (JA * tA) JA tA L := ⟨mA.1, fJA, ftA, fL, by nlinarith, by nlinarith, by nlinarith,
    by nlinarith, by linarith, by linarith, hL0, by linarith⟩
  -- `R = t + a / j` is `2 t` within `2 u`
  have haj1 : t * (1 - 2 / 16777216) ≤ a / j := by
    rw [le_div_iff₀ hJp]; nlinarith
  have haj2 : a / j ≤ t * (1 + 2 / 16777216) := by
    rw [div_le_iff₀ hJp]; nlinarith
  set R := t + a / j with hRd
  have hR1 : 2 * t * (1 - 1 / 16777216) ≤ R := by linarith
  have hR2 : R ≤ 2 * t * (1 + 1 / 16777216) := by linarith
  have hR0 : 0 < R := by nlinarith
  have hK : 4 * j * t ^ 3 = (j * t) * (2 * t) ^ 2 := by ring
  have hAR2hi : a * R ^ 2 ≤ L.toReal * (1 + 1 / 10 ^ 4) := by
    have h1 : a * R ^ 2 ≤ (j * t * (1 + 2 / 16777216)) * (2 * t * (1 + 1 / 16777216)) ^ 2 :=
      mul_le_mul ahi (pow_le_pow_left₀ hR0.le hR2 2) (by positivity) (by positivity)
    have h2 : (j * t * (1 + 2 / 16777216)) * (2 * t * (1 + 1 / 16777216)) ^ 2 =
        4 * j * t ^ 3 * ((1 + 2 / 16777216) * (1 + 1 / 16777216) ^ 2) := by ring
    have h3 : 4 * j * t ^ 3 * ((1 + 2 / 16777216) * (1 + 1 / 16777216) ^ 2) ≤
        L.toReal * (1 + 1 / 10 ^ 5) * ((1 + 2 / 16777216) * (1 + 1 / 16777216) ^ 2) := by gcongr
    have h4 : L.toReal * (1 + 1 / 10 ^ 5) * ((1 + 2 / 16777216) * (1 + 1 / 16777216) ^ 2) ≤
        L.toReal * (1 + 1 / 10 ^ 4) := by
      rw [mul_assoc]; gcongr; norm_num
    linarith
  have hAR2lo : min (12 / 100) (L.toReal * (1 - 1 / 10 ^ 5)) * (1 - 4 / 16777216) ≤ a * R ^ 2 := by
    have h1 : (j * t * (1 - 2 / 16777216)) * (2 * t * (1 - 1 / 16777216)) ^ 2 ≤ a * R ^ 2 :=
      mul_le_mul alo (pow_le_pow_left₀ (by positivity) hR1 2) (by positivity) ha0.le
    have h2 : (j * t * (1 - 2 / 16777216)) * (2 * t * (1 - 1 / 16777216)) ^ 2 =
        4 * j * t ^ 3 * ((1 - 2 / 16777216) * (1 - 1 / 16777216) ^ 2) := by ring
    have h3 : min (12 / 100) (L.toReal * (1 - 1 / 10 ^ 5)) * (1 - 4 / 16777216) ≤
        4 * j * t ^ 3 * ((1 - 2 / 16777216) * (1 - 1 / 16777216) ^ 2) := by
      have : (1 - 4 / 16777216 : ℝ) ≤ (1 - 2 / 16777216) * (1 - 1 / 16777216) ^ 2 := by norm_num
      have h0 : 0 ≤ min (12 / 100) (L.toReal * (1 - 1 / 10 ^ 5)) := le_min (by norm_num) (by nlinarith)
      calc _ ≤ min (12 / 100) (L.toReal * (1 - 1 / 10 ^ 5)) * ((1 - 2 / 16777216) * (1 - 1 / 16777216) ^ 2) := by
            gcongr
        _ ≤ _ := by gcongr
    linarith
  have h0 : SC.p7 a R 0 ≤ L.toReal * (1 + 1 / 10 ^ 4) := by
    rw [p7_expand]; simpa using hAR2hi
  have hl : L.toReal ≤ 200 * a * R ^ 2 := by
    rcases min_choice (12 / 100 : ℝ) (L.toReal * (1 - 1 / 10 ^ 5)) with hm | hm <;> rw [hm] at hAR2lo
    · nlinarith
    · nlinarith
  obtain ⟨f4, h40, hp⟩ := p7_t4_bound hL hQ fV (by rw [abs_of_pos (by linarith)]; linarith)
    (by rw [← hRd]; linarith) h0
  rw [← hRd] at hp
  set t4 := (t4F (JA * tA) JA tA L Vm).toReal
  have h410 : t4 ≤ 3 := by
    refine t4_le_three ha0 hR0 (by nlinarith) h40 hp (by linarith) ?_
    rcases min_choice (12 / 100 : ℝ) (L.toReal * (1 - 1 / 10 ^ 5)) with hm | hm <;> rw [hm] at hAR2lo
    · left
      by_contra hc
      have : R ^ 2 ≤ (2 * (21 / 100) * (1 + 1 / 16777216)) ^ 2 := pow_le_pow_left₀ hR0.le (by nlinarith) 2
      nlinarith
    · right; nlinarith
  have c1 : j * t ≤ a * (1 + 1 / 10 ^ 6) := by nlinarith
  have c2 : 2 * t ≤ R * (1 + 1 / 10 ^ 6) := by nlinarith
  have he4 := eff_le h40
  have he40 := eff_nonneg t4
  refine cpok_mk fJA ftA f32_isFinite_0p0 f4 hJp (by nlinarith) ht0 (by linarith)
    (by rw [e0]; norm_num) (by rw [e0]; norm_num) h40 h410 hA' ?_ ?_
  · rw [e0, eff_zero, add_zero, add_zero]
    calc SC.p7 (j * t) (2 * t) (eff t4) ≤ SC.p7 (j * t) (2 * t) t4 :=
          SC.p7_mono (by positivity) (by positivity) (eff_nonneg _) he4
      _ ≤ SC.p7 (a * (1 + 1 / 10 ^ 6)) (R * (1 + 1 / 10 ^ 6)) t4 :=
          SC.p7_mono_AR (by positivity) (by positivity) h40 c1 c2
      _ ≤ (1 + 1 / 10 ^ 6) ^ 3 * SC.p7 a R t4 := p7_scale ha0.le hR0.le h40 (by norm_num)
      _ ≤ (1 + 1 / 10 ^ 6) ^ 3 * (L.toReal * (1 + 1 / 2000)) := by gcongr
      _ ≤ L.toReal * (1 + 1 / 1000) := by nlinarith
  · rw [e0, eff_zero, add_zero, add_zero]
    have hmono : 4 * j * t ^ 3 ≤ SC.p7 (j * t) (2 * t) (eff t4) := by
      rw [← hp0]; exact SC.p7_mono (by positivity) (by positivity) le_rfl he40
    have hv : j * t * (2 * t) ≤ j * t * (2 * t + eff t4) := by
      have : 0 ≤ j * t := by positivity
      nlinarith
    rcases min_choice (12 / 100 : ℝ) (L.toReal * (1 - 1 / 10 ^ 5)) with hm | hm <;> rw [hm] at hK2
    · exact Or.inr ((hlow0 hK2).trans hv)
    · left; nlinarith

/-- In the long branch (`|At| ≥ Jm tj`) the half leg is at least `0.13 m`. -/
theorem branchB_L {Jm T At L : Float32} (fJ : Jm.IsFinite) (hJ : 49 / 10 ≤ Jm.toReal ∧ Jm.toReal ≤ 51 / 10)
    (fT : T.IsFinite) (hT : 19 / 100 ≤ T.toReal ∧ T.toReal ≤ 21 / 100) (fAt : At.IsFinite)
    (hAt0 : 0 < At.toReal) (hAtL : At.toReal ≤ 7 * L.toReal) (hc4 : ¬At.abs < Jm * T) :
    (Jm * T).IsFinite ∧ Jm.toReal * T.toReal * (1 - 2 / 16777216) ≤ |At.toReal| ∧ 13 / 100 ≤ L.toReal := by
  have m := R32.mul_ex fJ fT (by rw [abs_of_pos (by nlinarith)]; nlinarith)
    (by rw [abs_of_pos (by nlinarith)]; nlinarith)
  obtain ⟨mlo, -⟩ := m.bounds (by nlinarith)
  have h := (Float32.lt_iff_toReal_lt ((Float32.isFinite_abs At).2 fAt) m.1).not.1 hc4
  rw [Float32.toReal_abs, not_lt] at h
  refine ⟨m.1, mlo.trans h, ?_⟩
  have : |At.toReal| = At.toReal := by
    rw [abs_eq_self]; exact hAt0.le
  rw [this] at h
  nlinarith

set_option maxHeartbeats 4000000 in
/-- **The cubic branch is not taken**: with the mission's margins (`hB`), neither of its tests holds
in `float`. -/
theorem branchB_noB0 {Jm Am Vm L T : Float32} (fJ : Jm.IsFinite)
    (hJ : 49 / 10 ≤ Jm.toReal ∧ Jm.toReal ≤ 51 / 10) (fA : Am.IsFinite)
    (hA : 99 / 100 ≤ Am.toReal ∧ Am.toReal ≤ 182 / 100) (fV : Vm.IsFinite) (fL : L.IsFinite)
    (fT : T.IsFinite) (hT : 19 / 100 ≤ T.toReal ∧ T.toReal ≤ 21 / 100)
    (hB : Am.toReal * (21 / 100) + Am.toReal ^ 2 / (49 / 10) + 1 / 100 ≤ Vm.toReal ∧
      Am.toReal * (21 / 100 + Am.toReal / (49 / 10)) ^ 2 + 1 / 100 ≤ L.toReal)
    (h : Vm < 0.0 + Am * T + Am * Am / Jm ∨
      L < 1.0 / (Jm * Jm) * (Am * Am * Am + Am * Jm * (0.0 * 2.0 + Am * T * 2.0)) + 0.0 * T * 2.0 +
        Am * (T * T)) : False := by
  have hJ0 : 0 < Jm.toReal := by linarith
  have hA0 : 0 < Am.toReal := by linarith
  have bA := B32.of_exact fA (R := 2) (by rw [abs_of_pos hA0]; linarith)
  have bJ := B32.of_exact fJ (R := 6) (by rw [abs_of_pos hJ0]; linarith)
  have bT := B32.of_exact fT (R := 1 / 4) (by rw [abs_of_pos (by linarith)]; linarith)
  have b0 := B32.of_exact f32_isFinite_0p0 (R := 0) (by rw [f32_toReal_0p0]; simp)
  have b1 := B32.of_exact f32_isFinite_1p0 (R := 1) (by rw [f32_toReal_1p0]; simp)
  have b2 := B32.of_exact f32_isFinite_2p0 (R := 2) (by rw [f32_toReal_2p0]; norm_num)
  have m1 := B32.mul (e := 1 / 10 ^ 7) (R := 1 / 2) bA bT (by norm_num [capF]) (by norm_num) (by norm_num)
  have bAA := B32.mul (e := 1 / 10 ^ 6) (R := 4) bA bA (by norm_num [capF]) (by norm_num) (by norm_num)
  rcases h with h | h
  · have s1 := B32.add (e := 2 / 10 ^ 7) (R := 1 / 2) b0 m1 (by norm_num) (by norm_num [capF]) (by norm_num)
    have d1 := B32.div (e := 1 / 10 ^ 6) (R := 1) (mlo := 49 / 10) bAA bJ
      (by rw [abs_of_pos hJ0]; exact hJ.1) (by norm_num) (by norm_num) (by norm_num [capF]) (by norm_num)
    have s2 := B32.add (e := 2 / 10 ^ 6) (R := 3 / 2) s1 d1 (by norm_num) (by norm_num [capF]) (by norm_num)
    have hh := (Float32.lt_iff_toReal_lt fV s2.1.1).1 h
    have e := (abs_le.1 s2.1.2).2
    rw [f32_toReal_0p0] at e
    have q1 : Am.toReal * T.toReal ≤ Am.toReal * (21 / 100) := by nlinarith
    have q2 : Am.toReal * Am.toReal / Jm.toReal ≤ Am.toReal ^ 2 / (49 / 10) := by
      rw [div_le_div_iff₀ hJ0 (by norm_num)]; nlinarith
    linarith [hB.1]
  · have jj := B32.mul (e := 1 / 10 ^ 5) (R := 36) bJ bJ (by norm_num [capF]) (by norm_num) (by norm_num)
    have inv := B32.div (e := 1 / 10 ^ 6) (R := 1 / 24) (mlo := 24) b1 jj
      (by rw [abs_of_pos (by nlinarith)]; nlinarith) (by norm_num) (by norm_num)
      (by norm_num [capF]) (by norm_num)
    have aaa := B32.mul (e := 1 / 10 ^ 5) (R := 8) bAA bA (by norm_num [capF]) (by norm_num) (by norm_num)
    have aj := B32.mul (e := 1 / 10 ^ 5) (R := 12) bA bJ (by norm_num [capF]) (by norm_num) (by norm_num)
    have z2 := B32.mul (e := 1 / 10 ^ 10) (R := 0) b0 b2 (by norm_num [capF]) (by norm_num) (by norm_num)
    have at2 := B32.mul (e := 1 / 10 ^ 6) (R := 1) m1 b2 (by norm_num [capF]) (by norm_num) (by norm_num)
    have sum1 := B32.add (e := 1 / 10 ^ 5) (R := 1) z2 at2 (by norm_num) (by norm_num [capF]) (by norm_num)
    have ajs := B32.mul (e := 1 / 10 ^ 3) (R := 12) aj sum1 (by norm_num [capF]) (by norm_num) (by norm_num)
    have big := B32.add (e := 2 / 10 ^ 3) (R := 20) aaa ajs (by norm_num) (by norm_num [capF]) (by norm_num)
    have prod := B32.mul (e := 1 / 10 ^ 3) (R := 1) inv big (by norm_num [capF]) (by norm_num) (by norm_num)
    have z3 := B32.mul (e := 1 / 10 ^ 10) (R := 0) b0 bT (by norm_num [capF]) (by norm_num) (by norm_num)
    have z4 := B32.mul (e := 1 / 10 ^ 9) (R := 0) z3 b2 (by norm_num [capF]) (by norm_num) (by norm_num)
    have sum2 := B32.add (e := 2 / 10 ^ 3) (R := 1) prod z4 (by norm_num) (by norm_num [capF]) (by norm_num)
    have tt := B32.mul (e := 1 / 10 ^ 7) (R := 1 / 16) bT bT (by norm_num [capF]) (by norm_num) (by norm_num)
    have att := B32.mul (e := 1 / 10 ^ 6) (R := 1 / 8) bA tt (by norm_num [capF]) (by norm_num) (by norm_num)
    have X := B32.add (e := 3 / 10 ^ 3) (R := 2) sum2 att (by norm_num) (by norm_num [capF]) (by norm_num)
    have hh := (Float32.lt_iff_toReal_lt fL X.1.1).1 h
    have e := (abs_le.1 X.1.2).2
    simp only [f32_toReal_0p0, f32_toReal_1p0, f32_toReal_2p0] at e
    have hid : 1 / (Jm.toReal * Jm.toReal) * (Am.toReal * Am.toReal * Am.toReal + Am.toReal * Jm.toReal *
        (0 * 2 + Am.toReal * T.toReal * 2)) + 0 * T.toReal * 2 + Am.toReal * (T.toReal * T.toReal) =
        Am.toReal * (Am.toReal / Jm.toReal + T.toReal) ^ 2 := by
      field_simp; ring
    rw [hid] at e
    have q1 : Am.toReal / Jm.toReal + T.toReal ≤ 21 / 100 + Am.toReal / (49 / 10) := by
      have : Am.toReal / Jm.toReal ≤ Am.toReal / (49 / 10) :=
        div_le_div_of_nonneg_left hA0.le (by norm_num) hJ.1
      linarith
    have q2 : Am.toReal * (Am.toReal / Jm.toReal + T.toReal) ^ 2 ≤
        Am.toReal * (21 / 100 + Am.toReal / (49 / 10)) ^ 2 := by
      gcongr
      exact add_nonneg (div_nonneg hA0.le hJ0.le) (by linarith)
    linarith [hB.2]


set_option maxHeartbeats 4000000 in
/-- **The long branch's output** (`t₂ = Am/Jm - tj`, `t₄` from the quadratic root) satisfies `CPOk`. -/
theorem branchB_ok (hL : LibmSpec) {Jm Am Vm L T : Float32} (fJ : Jm.IsFinite)
    (hJ : 49 / 10 ≤ Jm.toReal ∧ Jm.toReal ≤ 51 / 10) (fA : Am.IsFinite)
    (hA : 99 / 100 ≤ Am.toReal ∧ Am.toReal ≤ 182 / 100) (fV : Vm.IsFinite)
    (hV : 99 / 100 ≤ Vm.toReal ∧ Vm.toReal ≤ 271 / 100) (fL : L.IsFinite)
    (hL13 : 13 / 100 ≤ L.toReal) (hL1 : L.toReal ≤ 181 / 100)
    (fT : T.IsFinite) (hT : 19 / 100 ≤ T.toReal ∧ T.toReal ≤ 21 / 100)
    (hJT : Jm.toReal * T.toReal * (1 - 2 / 16777216) ≤ Am.toReal)
    (hB : Am.toReal * (21 / 100 + Am.toReal / (49 / 10)) ^ 2 + 1 / 100 ≤ L.toReal) :
    CPOk L.toReal (Jm, T, Am / Jm - T, t4F Am Jm T L Vm, Am / Jm - T) := by
  have hJ0 : 0 < Jm.toReal := by linarith
  have hA0 : 0 < Am.toReal := by linarith
  have hT0 : 0 < T.toReal := by linarith
  have hq : Jm.toReal * (Am.toReal / Jm.toReal) = Am.toReal := by field_simp
  have hq1 : Am.toReal / Jm.toReal ≤ 182 / 100 / (49 / 10) := by
    rw [div_le_div_iff₀ hJ0 (by norm_num)]; nlinarith
  have hq0 : 0 < Am.toReal / Jm.toReal := div_pos hA0 hJ0
  -- `t₂` within `2·10⁻⁷` of `Am/Jm - tj`
  have dq := R32.div (k := 2) (R32.of_exact fA (le_refl (0 : ℝ))) (R32.of_exact fJ (le_refl (0 : ℝ)))
    le_rfl le_rfl (by norm_num) (by norm_num) hJ0.ne'
    (by rw [abs_of_pos hq0, le_div_iff₀ hJ0]; nlinarith)
    (by rw [abs_of_pos hq0, div_le_iff₀ hJ0]; nlinarith) (by norm_num)
  have bq : B32 (Am / Jm) (Am.toReal / Jm.toReal) (5 / 10 ^ 8) (1 / 2) := by
    refine ⟨⟨dq.1, dq.2.trans ?_⟩, by rw [abs_of_pos hq0]; linarith⟩
    rw [abs_of_pos hq0]; nlinarith
  have bT := B32.of_exact fT (R := 1 / 4) (by rw [abs_of_pos hT0]; linarith)
  have st := B32.sub (e := 2 / 10 ^ 7) (R := 1) bq bT (by norm_num) (by norm_num [capF]) (by norm_num)
  obtain ⟨e2lo, e2hi⟩ := abs_le.1 st.1.2
  have ft2 : (Am / Jm - T).IsFinite := st.1.1
  -- `t₂ > -FLT_EPSILON`: `Am/Jm ≥ tj (1 - 2u)` up to the division's rounding, then one subtraction
  have ht2 : -(1 / 2 ^ 23) < (Am / Jm - T).toReal := by
    have hqlo : Am.toReal / Jm.toReal * (1 - 2 / 16777216) ≤ (Am / Jm).toReal :=
      (dq.bounds hq0).1
    have hajt : T.toReal * (1 - 2 / 16777216) ≤ Am.toReal / Jm.toReal := by
      rw [le_div_iff₀ hJ0]; nlinarith
    have hm : |(Am / Jm).toReal - T.toReal| ≤ maxFinite32 := by
      have := capF_le_max32
      have h1 : |(Am / Jm).toReal - T.toReal| ≤ 1 := by
        rw [abs_le]; constructor <;> nlinarith [dq.bounds hq0]
      have : (1 : ℝ) ≤ capF := by norm_num [capF]
      linarith
    obtain ⟨-, es⟩ := Float32.sub_err_all dq.1 fT hm
    rw [show (2 : ℝ) ^ (-24 : ℤ) = 1 / 16777216 by norm_num] at es
    obtain ⟨es1, -⟩ := abs_le.1 es
    rcases le_total 0 ((Am / Jm).toReal - T.toReal) with hd | hd
    · rw [abs_of_nonneg hd] at es1; nlinarith
    · rw [abs_of_nonpos hd] at es1
      have : -(T.toReal * (4 / 16777216)) ≤ (Am / Jm).toReal - T.toReal := by nlinarith
      nlinarith
  set t2 := (Am / Jm - T).toReal
  set a := Am.toReal
  set j := Jm.toReal
  set t := T.toReal
  set R := t + a / j with hRd
  have hR0 : 19 / 100 ≤ R := by linarith
  have hR1 : R ≤ 21 / 100 + a / (49 / 10) := by
    have : a / j ≤ a / (49 / 10) := div_le_div_of_nonneg_left hA0.le (by norm_num) hJ.1
    linarith
  have hQ : QIn Am Jm T L := ⟨fA, fJ, fT, fL, by linarith, by linarith, by linarith, by linarith,
    by linarith, by linarith, by linarith, by linarith⟩
  have hAR2 : a * R ^ 2 ≤ a * (21 / 100 + a / (49 / 10)) ^ 2 := by
    gcongr
  have h0 : SC.p7 a R 0 ≤ L.toReal * (1 + 1 / 10 ^ 4) := by
    rw [p7_expand]; simp only [mul_zero, add_zero, zero_pow two_ne_zero, zero_div]; nlinarith
  have hl : L.toReal ≤ 200 * a * R ^ 2 := by
    have : (19 / 100 : ℝ) ^ 2 ≤ R ^ 2 := pow_le_pow_left₀ (by norm_num) hR0 2
    nlinarith
  obtain ⟨f4, h40, hp⟩ := p7_t4_bound hL hQ fV (by rw [abs_of_pos (by linarith)]; linarith) hl h0
  rw [← hRd] at hp
  set t4 := (t4F Am Jm T L Vm).toReal
  have h410 : t4 ≤ 3 := t4_le_three hA0 (by linarith) (by
    have : a / (49 / 10) ≤ 182 / 100 / (49 / 10) := by gcongr; exact hA.2
    linarith) h40 hp (by linarith) (Or.inl (by linarith))
  -- the accelerating phase with the durations `add_segments` gives
  have key : j * (t + eff t2) ≤ a * (1 + 1 / 10 ^ 5) ∧ 2 * t + eff t2 ≤ R * (1 + 1 / 10 ^ 5) := by
    rcases eff_cases t2 with ⟨he, -⟩ | ⟨he, -⟩ <;> rw [he]
    · constructor
      · have : j * (t + t2) ≤ j * (a / j + 2 / 10 ^ 7) := by
          apply mul_le_mul_of_nonneg_left _ hJ0.le; linarith
        rw [mul_add j (a / j), hq] at this; nlinarith
      · nlinarith
    · rw [add_zero, add_zero]
      constructor
      · nlinarith
      · have : t * (1 - 2 / 16777216) ≤ a / j := by
          rw [le_div_iff₀ hJ0]; nlinarith
        nlinarith
  have hA'0 : 0 ≤ j * (t + eff t2) := mul_nonneg hJ0.le (add_nonneg hT0.le (eff_nonneg _))
  have hR'0 : 0 ≤ 2 * t + eff t2 := add_nonneg (by linarith) (eff_nonneg _)
  have he2 := eff_nonneg t2
  have he4 := eff_nonneg t4
  refine cpok_mk fJ fT ft2 f4 hJ0 (by linarith) (by linarith) (by linarith) ht2 (by linarith) h40 h410
    (by nlinarith [key.1]) ?_ (Or.inr ?_)
  · calc SC.p7 (j * (t + eff t2)) (2 * t + eff t2) (eff t4)
        ≤ SC.p7 (j * (t + eff t2)) (2 * t + eff t2) t4 := SC.p7_mono hA'0 hR'0 (eff_nonneg _) (eff_le h40)
      _ ≤ SC.p7 (a * (1 + 1 / 10 ^ 5)) (R * (1 + 1 / 10 ^ 5)) t4 :=
          SC.p7_mono_AR hA'0 hR'0 h40 key.1 key.2
      _ ≤ (1 + 1 / 10 ^ 5) ^ 3 * SC.p7 a R t4 := p7_scale hA0.le (by linarith) h40 (by norm_num)
      _ ≤ (1 + 1 / 10 ^ 5) ^ 3 * (L.toReal * (1 + 1 / 2000)) := by gcongr
      _ ≤ L.toReal * (1 + 1 / 1000) := by nlinarith
  · have h1 : j * t ≤ j * (t + eff t2) := mul_le_mul_of_nonneg_left (by linarith) hJ0.le
    have h2 : 2 * t ≤ 2 * t + eff t2 + eff t4 := by linarith
    have h3 : (49 / 10 * (19 / 100)) * (2 * (19 / 100)) ≤ j * t * (2 * t) := by
      have h5 : 49 / 10 * (19 / 100) ≤ j * t := mul_le_mul hJ.1 hT.1 (by norm_num) hJ0.le
      exact mul_le_mul h5 (by linarith [hT.1]) (by norm_num) (by positivity)
    calc (1 / 4 : ℝ) ≤ j * t * (2 * t) := by linarith
      _ ≤ j * (t + eff t2) * (2 * t + eff t2 + eff t4) :=
          mul_le_mul h1 h2 (by linarith) hA'0

theorem cpok_ite {L : ℝ} {c : Prop} [Decidable c] {x y : Float32 × Float32 × Float32 × Float32 × Float32}
    (hx : c → CPOk L x) (hy : ¬c → CPOk L y) : CPOk L (if c then x else y) := by
  split_ifs with h
  exacts [hx h, hy h]

/-- The code's `t₄` (with `V0 = 0`) is `t4F`. -/
theorem t4code_eq (Am Jm tj L Vm : Float32) :
    MAX_float2 (MIN_float2 (-((0.0 : Float32) - Vm + Am * tj + (Am * Am) / Jm) / Am) (MAX_float2 (((Am * Am) * (-(3.0 : Float32) / (2.0 : Float32)) + safe_sqrt_float ((Am * Am * Am * Am) * ((1.0 : Float32) / (4.0 : Float32)) + (Jm * Jm) * ((0.0 : Float32) * (0.0 : Float32)) + (Am * Am) * (Jm * Jm) * (tj * tj) * ((1.0 : Float32) / (4.0 : Float32)) + Am * (Jm * Jm) * L * (2.0 : Float32) - (Am * Am) * Jm * (0.0 : Float32) + (Am * Am * Am) * Jm * tj * ((1.0 : Float32) / (2.0 : Float32)) - Am * (Jm * Jm) * (0.0 : Float32) * tj) - Jm * (0.0 : Float32) - Am * Jm * tj * ((3.0 : Float32) / (2.0 : Float32))) / (Am * Jm)) (((Am * Am) * (-(3.0 : Float32) / (2.0 : Float32)) - safe_sqrt_float ((Am * Am * Am * Am) * ((1.0 : Float32) / (4.0 : Float32)) + (Jm * Jm) * ((0.0 : Float32) * (0.0 : Float32)) + (Am * Am) * (Jm * Jm) * (tj * tj) * ((1.0 : Float32) / (4.0 : Float32)) + Am * (Jm * Jm) * L * (2.0 : Float32) - (Am * Am) * Jm * (0.0 : Float32) + (Am * Am * Am) * Jm * tj * ((1.0 : Float32) / (2.0 : Float32)) - Am * (Jm * Jm) * (0.0 : Float32) * tj) - Jm * (0.0 : Float32) - Am * Jm * tj * ((3.0 : Float32) / (2.0 : Float32))) / (Am * Jm)))) (0.0 : Float32) = t4F Am Jm tj L Vm := rfl

set_option maxHeartbeats 4000000 in
/-- **`calculate_path` on the mission's ranges**: finite outputs, no motion or an accelerating
phase within `L (1 + 1/1000)`; the cubic branch is excluded by the margins `hB`. -/
theorem calcPath_spec (hL : LibmSpec) {Sm Jm Am Vm L : Float32}
    (fS : Sm.IsFinite) (hS : 39 ≤ Sm.toReal ∧ Sm.toReal ≤ 40)
    (fJ : Jm.IsFinite) (hJ : 49 / 10 ≤ Jm.toReal ∧ Jm.toReal ≤ 51 / 10)
    (fA : Am.IsFinite) (hA : 99 / 100 ≤ Am.toReal ∧ Am.toReal ≤ 182 / 100)
    (fV : Vm.IsFinite) (hV : 99 / 100 ≤ Vm.toReal ∧ Vm.toReal ≤ 271 / 100)
    (fL : L.IsFinite) (hLL : 1 / 10 ^ 4 ≤ L.toReal ∧ L.toReal ≤ 181 / 100)
    (hB : 13 / 100 ≤ L.toReal →
      Am.toReal * (21 / 100) + Am.toReal ^ 2 / (49 / 10) + 1 / 100 ≤ Vm.toReal ∧
      Am.toReal * (21 / 100 + Am.toReal / (49 / 10)) ^ 2 + 1 / 100 ≤ L.toReal) :
    CPOk L.toReal (SCurve.calculate_path Sm Jm 0.0 Am Vm L 0.0 0.0 0.0 0.0 0.0) := by
  have hpf := R32.pi_f hL
  obtain ⟨⟨fT, -⟩, hT0, hT1⟩ := tj0_spec hL fS hS fJ hJ
  have e23 : (2 : ℝ) ^ (-23 : ℤ) = 1 / 2 ^ 23 := by norm_num
  have pS := (wp_isPos_iff fS).2 (by rw [e23]; linarith)
  have pJ := (wp_isPos_iff fJ).2 (by rw [e23]; linarith)
  have pA := (wp_isPos_iff fA).2 (by rw [e23]; linarith)
  have pV := (wp_isPos_iff fV).2 (by rw [e23]; linarith)
  have hL0 : 1 / 2 ^ 23 ≤ L.toReal := le_trans (by norm_num) hLL.1
  have pL := (wp_isPos_iff fL).2 (by rw [e23]; exact hL0)
  unfold SCurve.calculate_path
  simp only [Id.run, id_pure_eq, t4code_eq]
  generalize Float.toFloat32 3.1415926535897931 = pf at hpf fT hT0 hT1 ⊢
  generalize Jm * pf / (2.0 * Sm) = T at fT hT0 hT1 ⊢
  generalize hAtd : MIN_float2 (MIN_float2 Am ((Vm - 0.0) / (2.0 * T)))
    ((L - 4.0 * 0.0 * T) / (4.0 * sq_float T)) = At
  generalize htAd : MIN_float2 (MIN_float2 (MIN_float2 T ((L * pf / (8.0 * Sm)).pow (1.0 / 4.0)))
    ((Vm * pf / (4.0 * Sm)).pow (1.0 / 3.0))) (safe_sqrt_float (Am * pf / (2.0 * Sm))) = tA
  generalize hJAd : 2.0 * Sm * tA / pf = JA
  obtain ⟨fAt, hAtA, hAtL, hAtlo⟩ := At_spec fA hA.1 fV hV fL hL0 hLL.2 fT ⟨hT0, hT1⟩ hAtd
  have hAt0 := hAtlo hLL.1
  have pAt := (wp_isPos_iff fAt).2 (by rw [e23]; exact hAt0)
  rw [pS, pJ, pA, pV, pL, pAt]
  have c2 : ¬(0.0 : Float32) ≥ Vm := by
    intro h
    have := (Float32.le_iff_toReal_le fV f32_isFinite_0p0).1 h
    rw [f32_toReal_0p0] at this; linarith
  simp only [Bool.not_true, Bool.or_false, Bool.false_eq_true, ite_false, c2]
  split
  next c4 =>
    obtain ⟨ftA, ht0, ht1, fJA, hJ1, hJ2, hK1, hK2⟩ :=
      branchA_spec hL fS hS fA hA fV hV fL hL0 hLL.2 hpf fT ⟨hT0, hT1⟩ htAd hJAd
    have hok := branchA_ok hL fL hL0 hLL.2 fV hV ftA ht0 ht1 fJA hJ1 hJ2 hK1 hK2
    simp only [f32_isZero_zero, ite_true]
    split
    next => exact cpok_ite (fun c => absurd c (cpok_check hL hok.1)) (fun _ => hok.1)
    next => exact cpok_ite (fun c => absurd c (cpok_check hL hok.2)) (fun _ => hok.2)
  next c4 =>
    obtain ⟨-, hJT, hL13⟩ := branchB_L fJ hJ fT ⟨hT0, hT1⟩ fAt (by linarith) hAtL c4
    have hJT' : Jm.toReal * T.toReal * (1 - 2 / 16777216) ≤ Am.toReal := by
      rw [abs_of_pos (by linarith)] at hJT; linarith
    obtain ⟨hB1, hB2⟩ := hB hL13
    have hok := branchB_ok hL fJ hJ fA hA fV hV fL hL13 hLL.2 fT ⟨hT0, hT1⟩ hJT' hB2
    split
    next c12 =>
      simp only [Bool.or_eq_true, decide_eq_true_eq] at c12
      exact (branchB_noB0 fJ hJ fA hA fV fL fT ⟨hT0, hT1⟩ ⟨hB1, hB2⟩ c12).elim
    next => exact cpok_ite (fun c => absurd c (cpok_check hL hok)) (fun _ => hok)

end

end Contracts.Mission
