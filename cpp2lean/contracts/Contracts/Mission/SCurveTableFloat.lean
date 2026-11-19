import Contracts.Mission.SCurveEval
import Contracts.Mission.SCurveTableCode

/-!
# One entry of the `add_segments` table in `float`

Each entry written by `add_segment_incr_jerk`, `add_segment_decr_jerk`, `add_segment_const_jerk`
is within a small absolute error of the real node (`SC.incrNode`, `SC.decrNode`, `SC.constNode`)
computed from the previous entry's values, on given magnitude ranges of the previous entry
(generated chains of `B32` steps; the bounds are numerals checked by `norm_num`).
-/

namespace Contracts.Mission

open Float.Model UnpackedFloat AC_WPNav_lib

noncomputable section

namespace SCT

theorem f32_c43 : (4.0 : Float32) / (3.0 : Float32) = 1.33333337 := by decide +kernel
theorem f32_unpack_c43 : (1.33333337 : Float32).toModel.unpack =
    .finite .positive 11184811 (-23) (by decide) := by rfl
theorem f32_toReal_c43 : (1.33333337 : Float32).toReal = (11184811 / 8388608 : ℝ) := by
  rw [Float32.toReal, f32_unpack_c43]; simp [UnpackedFloat.toReal, Sign.apply]; norm_num
theorem f32_isFinite_c43 : (1.33333337 : Float32).IsFinite := by
  rw [Float32.isFinite_iff, f32_unpack_c43]; rfl

theorem sq_float_eq (x : Float32) : sq_float x = x * x := rfl

/-- `powf x 3` on `[0, D]`. -/
theorem B32.pow3 (hL : LibmSpec) {x : Float32} {D : ℝ} (fx : x.IsFinite) (h0 : 0 ≤ x.toReal)
    (h1 : x.toReal ≤ D) (hD : D ≤ 2 ^ 30) :
    B32 (Float32.pow x (3.0 : Float32)) (x.toReal ^ 3) (D ^ 3 / 4194304 + 1 / 2 ^ 150) (D ^ 3) := by
  have hx : |x.toReal| ≤ 2 ^ (30 : ℤ) := by
    rw [abs_of_nonneg h0]; have : (2 : ℝ) ^ (30 : ℤ) = 2 ^ 30 := by norm_num
    linarith
  obtain ⟨hf, he⟩ := hL.powf3 x fx hx
  have h3 : x.toReal ^ 3 ≤ D ^ 3 := pow_le_pow_left₀ h0 h1 3
  have h3' : 0 ≤ x.toReal ^ 3 := pow_nonneg h0 3
  refine ⟨⟨hf, ?_⟩, by rw [abs_of_nonneg h3']; exact h3⟩
  rw [abs_of_nonneg h3'] at he
  have e22 : (2 : ℝ) ^ (-22 : ℤ) = 1 / 4194304 := by norm_num
  have e150 : (2 : ℝ) ^ (-150 : ℤ) = 1 / 2 ^ 150 := by norm_num
  rw [e22, e150] at he
  have : 1 / 4194304 * x.toReal ^ 3 ≤ D ^ 3 / 4194304 := by linarith
  linarith

set_option maxHeartbeats 4000000 in
/-- The ramp constants `AT`, `VT`, `PT`, `A2T = J t_j`, `V2T = J t_j²`, `P2T`, `t_j²` of
`add_segment_incr_jerk`/`add_segment_decr_jerk`, with `b = π / t_j`. -/
theorem ramp_consts (hL : LibmSpec) {tj Jm : Float32} (ft : tj.IsFinite) (fJ : Jm.IsFinite)
    (ht0 : 1 / 300 ≤ tj.toReal) (ht1 : tj.toReal ≤ 1 / 4) (hJ : |Jm.toReal| ≤ 6) :
    B32 (Jm * (0.5 : Float32) * tj) (SC.rAT Jm.toReal tj.toReal) (179 / 2000000000) (3 / 4) ∧
    B32 (vtF tj Jm) (SC.rVT Jm.toReal (Real.pi / tj.toReal) tj.toReal) (301 / 5000000000) (33 / 250) ∧
    B32 (ptF tj Jm) (SC.rPT Jm.toReal (Real.pi / tj.toReal) tj.toReal) (413 / 50000000000) (63 / 5000) ∧
    B32 (Jm * tj) (Jm.toReal * tj.toReal) (179 / 2000000000) (3 / 2) ∧
    B32 (Jm * sq_float tj) (Jm.toReal * tj.toReal ^ 2) (7 / 156250000) (3 / 8) ∧
    B32 (p2tF tj Jm) (SC.rP2T Jm.toReal (Real.pi / tj.toReal) tj.toReal) (41 / 1000000000) (7209 / 100000) ∧
    B32 (sq_float tj) (tj.toReal ^ 2) (373 / 100000000000) (1 / 16) := by
  have hpf := R32.pi_f hL
  have pw := B32.pow3 hL ft (by linarith) ht1 (by norm_num)
  unfold vtF ptF p2tF betaF
  simp only [sq_float_eq]
  generalize Float.toFloat32 (3.1415926535897931 : Float) = pf at hpf ⊢
  have p3 := Real.pi_gt_three
  have p4 := Real.pi_lt_d2
  have p5 := Real.pi_gt_d2
  generalize hT : tj.toReal = T at *
  have hT0 : 0 < T := by linarith
  have hb12 : 12 ≤ Real.pi / T := by rw [le_div_iff₀ hT0]; linarith
  have hb1 : Real.pi / T ≤ 1000 := by rw [div_le_iff₀ hT0]; nlinarith
  generalize hb : Real.pi / T = b at hb12 hb1 ⊢
  have hβ : R32 (pf / tj) b 4 := by
    rw [← hb]
    have eTj : R32 tj T 0 := hT ▸ R32.of_exact ft le_rfl
    refine R32.div hpf eTj (by norm_num) le_rfl (by norm_num)
      (by norm_num) hT0.ne' ?_ ?_ (by norm_num)
    · rw [hb, abs_of_pos (by linarith)]; linarith
    · rw [hb, abs_of_pos (by linarith)]; linarith
  have hbb2 : R32 (pf / tj * (pf / tj)) (b * b) 10 := by
    refine R32.mul hβ hβ (by norm_num) (by norm_num) (by norm_num) (by norm_num) ?_ ?_ (by norm_num)
    · rw [abs_of_pos (by positivity)]; nlinarith
    · rw [abs_of_pos (by positivity)]; nlinarith
  have hbb : 157 ≤ |b * b| := by
    rw [abs_of_pos (by positivity)]
    have : 4 * Real.pi ≤ b := by rw [← hb, le_div_iff₀ hT0]; nlinarith
    nlinarith
  have eJ := B32.of_exact fJ hJ
  have eT : B32 tj T 0 (1 / 4) := B32.sce_lit ft hT (by rw [abs_of_pos hT0]; linarith)
  have eH : B32 (0.5 : Float32) (1 / 2) 0 (1 / 2) :=
    B32.sce_lit f32_isFinite_0p5 f32_toReal_0p5 (by norm_num)
  have e2 : B32 (2.0 : Float32) 2 0 2 := B32.sce_lit f32_isFinite_2p0 f32_toReal_2p0 (by norm_num)
  have e1 : B32 (1.0 : Float32) 1 0 1 := B32.sce_lit f32_isFinite_1p0 f32_toReal_1p0 (by norm_num)
  have c16 : B32 ((1.0 : Float32) / (6.0 : Float32)) (1 / 6) (1 / 201326592) (1 / 6) := by
    rw [sce_c6]; exact ⟨⟨sce_isFinite_c6, by rw [sce_toReal_c6]; norm_num⟩, by norm_num⟩
  have c43 : B32 ((4.0 : Float32) / (3.0 : Float32)) (4 / 3) (1 / 25165824) (4 / 3) := by
    rw [f32_c43]; exact ⟨⟨f32_isFinite_c43, by rw [f32_toReal_c43]; norm_num⟩, by norm_num⟩
  have pw : B32 (Float32.pow tj (3.0 : Float32)) (T ^ 3) (1 / 64 / 4194304 + 1 / 2 ^ 150) (1 / 64) :=
    pw.mono (by norm_num) (by norm_num)
  have b1 := B32.mul eJ eH (e := 179 / 10 ^ 9) (R := 3) (by sce_num) (by sce_num) (by sce_num)
  have b2 := B32.mul b1 eT (e := 895 / 10 ^ 10) (R := 7500 / 10 ^ 4) (by sce_num) (by sce_num) (by sce_num)
  have b3 := B32.mul eT eT (e := 373 / 10 ^ 11) (R := 6250 / 10 ^ 5) (by sce_num) (by sce_num) (by sce_num)
  have b4 := B32.mul b3 eH (e := 373 / 10 ^ 11) (R := 3125 / 10 ^ 5) (by sce_num) (by sce_num) (by sce_num)
  have b5 := B32.sce_divR e2 hbb2 (by norm_num) (by norm_num) hbb (by norm_num) (e := 836 / 10 ^ 11) (R := 1274 / 10 ^ 5) (by sce_num) (by sce_num) (by sce_num)
  have b6 := B32.sub b4 b5 (e := 148 / 10 ^ 10) (R := 4399 / 10 ^ 5) (by sce_num) (by sce_num) (by sce_num)
  have b7 := B32.mul b1 b6 (e := 602 / 10 ^ 10) (R := 1320 / 10 ^ 4) (by sce_num) (by sce_num) (by sce_num)
  have b8 := e1.neg
  have b9 := B32.sce_divR b8 hbb2 (by norm_num) (by norm_num) hbb (by norm_num) (e := 418 / 10 ^ 11) (R := 6370 / 10 ^ 6) (by sce_num) (by sce_num) (by sce_num)
  have b10 := B32.mul b9 eT (e := 114 / 10 ^ 11) (R := 1593 / 10 ^ 6) (by sce_num) (by sce_num) (by sce_num)
  have b11 := B32.mul c16 pw (e := 854 / 10 ^ 12) (R := 2605 / 10 ^ 6) (by sce_num) (by sce_num) (by sce_num)
  have b12 := B32.add b10 b11 (e := 225 / 10 ^ 11) (R := 4198 / 10 ^ 6) (by sce_num) (by sce_num) (by sce_num)
  have b13 := B32.mul b1 b12 (e := 826 / 10 ^ 11) (R := 1260 / 10 ^ 5) (by sce_num) (by sce_num) (by sce_num)
  have b14 := B32.mul eJ eT (e := 895 / 10 ^ 10) (R := 1500 / 10 ^ 3) (by sce_num) (by sce_num) (by sce_num)
  have b15 := B32.mul eJ b3 (e := 448 / 10 ^ 10) (R := 3750 / 10 ^ 4) (by sce_num) (by sce_num) (by sce_num)
  have b16 := B32.mul b9 e2 (e := 912 / 10 ^ 11) (R := 1274 / 10 ^ 5) (by sce_num) (by sce_num) (by sce_num)
  have b17 := B32.mul b16 eT (e := 247 / 10 ^ 11) (R := 3185 / 10 ^ 6) (by sce_num) (by sce_num) (by sce_num)
  have b18 := B32.mul c43 pw (e := 683 / 10 ^ 11) (R := 2084 / 10 ^ 5) (by sce_num) (by sce_num) (by sce_num)
  have b19 := B32.add b17 b18 (e := 108 / 10 ^ 10) (R := 2403 / 10 ^ 5) (by sce_num) (by sce_num) (by sce_num)
  have b20 := B32.mul b1 b19 (e := 410 / 10 ^ 10) (R := 7209 / 10 ^ 5) (by sce_num) (by sce_num) (by sce_num)
  have hb0 : b ≠ 0 := by linarith
  have r1 : B32 (Jm * (0.5 : Float32) * tj) (SC.rAT Jm.toReal T) (179 / 2000000000) (3 / 4) :=
    (b2.congr (by simp only [SC.rAT]; ring)).mono (by norm_num) (by norm_num)
  have r2 : B32 (Jm * (0.5 : Float32) * (tj * tj * (0.5 : Float32) - (2.0 : Float32) / (pf / tj * (pf / tj))))
      (SC.rVT Jm.toReal b T) (301 / 5000000000) (33 / 250) :=
    (b7.congr (by simp only [SC.rVT]; ring)).mono (by norm_num) (by norm_num)
  have r3 : B32 (Jm * (0.5 : Float32) * (-(1.0 : Float32) / (pf / tj * (pf / tj)) * tj +
      (1.0 : Float32) / (6.0 : Float32) * Float32.pow tj (3.0 : Float32)))
      (SC.rPT Jm.toReal b T) (413 / 50000000000) (63 / 5000) :=
    (b13.congr (by simp only [SC.rPT]; ring)).mono (by norm_num) (by norm_num)
  have r4 : B32 (Jm * tj) (Jm.toReal * T) (179 / 2000000000) (3 / 2) :=
    b14.mono (by norm_num) (by norm_num)
  have r5 : B32 (Jm * (tj * tj)) (Jm.toReal * T ^ 2) (7 / 156250000) (3 / 8) :=
    (b15.congr (by ring)).mono (by norm_num) (by norm_num)
  have r6 : B32 (Jm * (0.5 : Float32) * (-(1.0 : Float32) / (pf / tj * (pf / tj)) * (2.0 : Float32) * tj +
      (4.0 : Float32) / (3.0 : Float32) * Float32.pow tj (3.0 : Float32)))
      (SC.rP2T Jm.toReal b T) (41 / 1000000000) (7209 / 100000) :=
    (b20.congr (by simp only [SC.rP2T]; ring)).mono (by norm_num) (by norm_num)
  have r7 : B32 (tj * tj) (T ^ 2) (373 / 100000000000) (1 / 16) :=
    (b3.congr (by ring)).mono (by norm_num) (by norm_num)
  exact ⟨r1, r2, r3, r4, r5, r6, r7⟩

theorem zero_mul_val {x z : Float32} (hx : x.IsFinite) (hz : z.IsFinite) (h0 : z.toReal = 0) :
    (z * x).IsFinite ∧ (z * x).toReal = 0 := by
  have := Float32.mul_exact hz hx hz (by rw [h0, zero_mul])
  rwa [h0] at this

theorem B32.add_zero' {x z : Float32} {r e R : ℝ} (hx : B32 x r e R) (hz : z.IsFinite)
    (h0 : z.toReal = 0) : B32 (x + z) r e R := by
  obtain ⟨f, v⟩ := Float32.add_zero_val hx.1.1 hz h0
  exact ⟨⟨f, by rw [v]; exact hx.1.2⟩, hx.2⟩

macro "fl_num" : tactic => `(tactic| norm_num [capF])

macro "node_eq" : tactic => `(tactic| first
  | (simp only [SC.constNode, SC.cA, SC.cV, SC.cP, SC.incrNode, SC.decrNode, SC.rAT]; done)
  | (simp only [SC.constNode, SC.cA, SC.cV, SC.cP, SC.incrNode, SC.decrNode, SC.rAT]; ring))

set_option maxHeartbeats 4000000 in
theorem fl_incr_G (hL : LibmSpec) {A0 V0 P0 tj Jm : Float32} (fA : A0.IsFinite) (fV : V0.IsFinite)
    (fP : P0.IsFinite) (ft : tj.IsFinite) (fJ : Jm.IsFinite) (ht0 : 1 / 300 ≤ tj.toReal)
    (ht1 : tj.toReal ≤ 1 / 4) (hJ : |Jm.toReal| ≤ 6) (hA : |A0.toReal| ≤ 2001 / 1000)
    (hV : |V0.toReal| ≤ 3001 / 1000) (hP : |P0.toReal| ≤ 4001 / 1000) :
    A32 (A0 + Jm * (0.5 : Float32) * tj) (SC.incrNode ⟨A0.toReal, V0.toReal, P0.toReal⟩ Jm.toReal (Real.pi / tj.toReal) tj.toReal).a (127 / 500000000) ∧
    A32 (V0 + A0 * tj + vtF tj Jm) (SC.incrNode ⟨A0.toReal, V0.toReal, P0.toReal⟩ Jm.toReal (Real.pi / tj.toReal) tj.toReal).v (129 / 250000000) ∧
    A32 (P0 + V0 * tj + (0.5 : Float32) * A0 * sq_float tj + ptF tj Jm) (SC.incrNode ⟨A0.toReal, V0.toReal, P0.toReal⟩ Jm.toReal (Real.pi / tj.toReal) tj.toReal).p (37 / 40000000) := by
  obtain ⟨cAT, cVT, cPT, cA2T, cV2T, cP2T, csq⟩ := ramp_consts hL ft fJ ht0 ht1 hJ
  have eA := B32.of_exact fA hA
  have eV := B32.of_exact fV hV
  have eP := B32.of_exact fP hP
  have eT : B32 tj tj.toReal 0 (1 / 4) := B32.of_exact ft (by rw [abs_of_pos (by linarith)]; exact ht1)
  have eH : B32 (0.5 : Float32) (1 / 2) 0 (1 / 2) :=
    B32.sce_lit f32_isFinite_0p5 f32_toReal_0p5 (by norm_num)
  have b1 := B32.add eA cAT (e := 254 / 10 ^ 9) (R := 2751 / 10 ^ 3) (by fl_num) (by fl_num) (by fl_num)
  have b2 := B32.mul eA eT (e := 299 / 10 ^ 10) (R := 5003 / 10 ^ 4) (by fl_num) (by fl_num) (by fl_num)
  have b3 := B32.add eV b2 (e := 239 / 10 ^ 9) (R := 3502 / 10 ^ 3) (by fl_num) (by fl_num) (by fl_num)
  have b4 := B32.add b3 cVT (e := 516 / 10 ^ 9) (R := 3634 / 10 ^ 3) (by fl_num) (by fl_num) (by fl_num)
  have b5 := B32.mul eV eT (e := 448 / 10 ^ 10) (R := 7503 / 10 ^ 4) (by fl_num) (by fl_num) (by fl_num)
  have b6 := B32.add eP b5 (e := 329 / 10 ^ 9) (R := 4752 / 10 ^ 3) (by fl_num) (by fl_num) (by fl_num)
  have b7 := B32.mul eH eA (e := 597 / 10 ^ 10) (R := 1001 / 10 ^ 3) (by fl_num) (by fl_num) (by fl_num)
  have b8 := B32.mul b7 csq (e := 112 / 10 ^ 10) (R := 6257 / 10 ^ 5) (by fl_num) (by fl_num) (by fl_num)
  have b9 := B32.add b6 b8 (e := 628 / 10 ^ 9) (R := 4815 / 10 ^ 3) (by fl_num) (by fl_num) (by fl_num)
  have b10 := B32.add b9 cPT (e := 925 / 10 ^ 9) (R := 4828 / 10 ^ 3) (by fl_num) (by fl_num) (by fl_num)
  refine ⟨(b1.1.congr (by node_eq)).mono (by norm_num),
    (b4.1.congr (by node_eq)).mono (by norm_num), (b10.1.congr (by node_eq)).mono (by norm_num)⟩

set_option maxHeartbeats 4000000 in
theorem fl_decr_G (hL : LibmSpec) {A0 V0 P0 tj Jm : Float32} (fA : A0.IsFinite) (fV : V0.IsFinite)
    (fP : P0.IsFinite) (ft : tj.IsFinite) (fJ : Jm.IsFinite) (ht0 : 1 / 300 ≤ tj.toReal)
    (ht1 : tj.toReal ≤ 1 / 4) (hJ : |Jm.toReal| ≤ 6) (hA : |A0.toReal| ≤ 2001 / 1000)
    (hV : |V0.toReal| ≤ 3001 / 1000) (hP : |P0.toReal| ≤ 4001 / 1000) :
    A32 (A0 - Jm * (0.5 : Float32) * tj + Jm * tj) (SC.decrNode ⟨A0.toReal, V0.toReal, P0.toReal⟩ Jm.toReal (Real.pi / tj.toReal) tj.toReal).a (597 / 1000000000) ∧
    A32 (V0 - vtF tj Jm + (A0 - Jm * (0.5 : Float32) * tj) * tj + Jm * sq_float tj) (SC.decrNode ⟨A0.toReal, V0.toReal, P0.toReal⟩ Jm.toReal (Real.pi / tj.toReal) tj.toReal).v (7 / 8000000) ∧
    A32 (P0 - ptF tj Jm + (V0 - vtF tj Jm) * tj + (0.5 : Float32) * (A0 - Jm * (0.5 : Float32) * tj) * sq_float tj + p2tF tj Jm) (SC.decrNode ⟨A0.toReal, V0.toReal, P0.toReal⟩ Jm.toReal (Real.pi / tj.toReal) tj.toReal).p (13 / 10000000) := by
  obtain ⟨cAT, cVT, cPT, cA2T, cV2T, cP2T, csq⟩ := ramp_consts hL ft fJ ht0 ht1 hJ
  have eA := B32.of_exact fA hA
  have eV := B32.of_exact fV hV
  have eP := B32.of_exact fP hP
  have eT : B32 tj tj.toReal 0 (1 / 4) := B32.of_exact ft (by rw [abs_of_pos (by linarith)]; exact ht1)
  have eH : B32 (0.5 : Float32) (1 / 2) 0 (1 / 2) :=
    B32.sce_lit f32_isFinite_0p5 f32_toReal_0p5 (by norm_num)
  have b1 := B32.sub eA cAT (e := 254 / 10 ^ 9) (R := 2751 / 10 ^ 3) (by fl_num) (by fl_num) (by fl_num)
  have b2 := B32.add b1 cA2T (e := 597 / 10 ^ 9) (R := 4251 / 10 ^ 3) (by fl_num) (by fl_num) (by fl_num)
  have b3 := B32.sub eV cVT (e := 247 / 10 ^ 9) (R := 3133 / 10 ^ 3) (by fl_num) (by fl_num) (by fl_num)
  have b4 := B32.mul b1 eT (e := 105 / 10 ^ 9) (R := 6878 / 10 ^ 4) (by fl_num) (by fl_num) (by fl_num)
  have b5 := B32.add b3 b4 (e := 580 / 10 ^ 9) (R := 3821 / 10 ^ 3) (by fl_num) (by fl_num) (by fl_num)
  have b6 := B32.add b5 cV2T (e := 875 / 10 ^ 9) (R := 4196 / 10 ^ 3) (by fl_num) (by fl_num) (by fl_num)
  have b7 := B32.sub eP cPT (e := 248 / 10 ^ 9) (R := 4014 / 10 ^ 3) (by fl_num) (by fl_num) (by fl_num)
  have b8 := B32.mul b3 eT (e := 109 / 10 ^ 9) (R := 7833 / 10 ^ 4) (by fl_num) (by fl_num) (by fl_num)
  have b9 := B32.add b7 b8 (e := 643 / 10 ^ 9) (R := 4798 / 10 ^ 3) (by fl_num) (by fl_num) (by fl_num)
  have b10 := B32.mul eH b1 (e := 209 / 10 ^ 9) (R := 1376 / 10 ^ 3) (by fl_num) (by fl_num) (by fl_num)
  have b11 := B32.mul b10 csq (e := 234 / 10 ^ 10) (R := 8600 / 10 ^ 5) (by fl_num) (by fl_num) (by fl_num)
  have b12 := B32.add b9 b11 (e := 958 / 10 ^ 9) (R := 4884 / 10 ^ 3) (by fl_num) (by fl_num) (by fl_num)
  have b13 := B32.add b12 cP2T (e := 130 / 10 ^ 8) (R := 4957 / 10 ^ 3) (by fl_num) (by fl_num) (by fl_num)
  refine ⟨(b2.1.congr (by node_eq)).mono (by norm_num),
    (b6.1.congr (by node_eq)).mono (by norm_num), (b13.1.congr (by node_eq)).mono (by norm_num)⟩

set_option maxHeartbeats 4000000 in
theorem fl_incr_S (hL : LibmSpec) {A0 V0 P0 tj Jm : Float32} (fA : A0.IsFinite) (fV : V0.IsFinite)
    (fP : P0.IsFinite) (ft : tj.IsFinite) (fJ : Jm.IsFinite) (ht0 : 1 / 300 ≤ tj.toReal)
    (ht1 : tj.toReal ≤ 1 / 4) (hJ : |Jm.toReal| ≤ 6) (hA : |A0.toReal| ≤ 2001 / 1000)
    (hV : |V0.toReal| ≤ 613 / 2500) (hP : |P0.toReal| ≤ 19 / 1250) :
    A32 (A0 + Jm * (0.5 : Float32) * tj) (SC.incrNode ⟨A0.toReal, V0.toReal, P0.toReal⟩ Jm.toReal (Real.pi / tj.toReal) tj.toReal).a (127 / 500000000) ∧
    A32 (V0 + A0 * tj + vtF tj Jm) (SC.incrNode ⟨A0.toReal, V0.toReal, P0.toReal⟩ Jm.toReal (Real.pi / tj.toReal) tj.toReal).v (187 / 1000000000) ∧
    A32 (P0 + V0 * tj + (0.5 : Float32) * A0 * sq_float tj + ptF tj Jm) (SC.incrNode ⟨A0.toReal, V0.toReal, P0.toReal⟩ Jm.toReal (Real.pi / tj.toReal) tj.toReal).p (113 / 2500000000) := by
  obtain ⟨cAT, cVT, cPT, cA2T, cV2T, cP2T, csq⟩ := ramp_consts hL ft fJ ht0 ht1 hJ
  have eA := B32.of_exact fA hA
  have eV := B32.of_exact fV hV
  have eP := B32.of_exact fP hP
  have eT : B32 tj tj.toReal 0 (1 / 4) := B32.of_exact ft (by rw [abs_of_pos (by linarith)]; exact ht1)
  have eH : B32 (0.5 : Float32) (1 / 2) 0 (1 / 2) :=
    B32.sce_lit f32_isFinite_0p5 f32_toReal_0p5 (by norm_num)
  have b1 := B32.add eA cAT (e := 254 / 10 ^ 9) (R := 2751 / 10 ^ 3) (by fl_num) (by fl_num) (by fl_num)
  have b2 := B32.mul eA eT (e := 299 / 10 ^ 10) (R := 5003 / 10 ^ 4) (by fl_num) (by fl_num) (by fl_num)
  have b3 := B32.add eV b2 (e := 744 / 10 ^ 10) (R := 7455 / 10 ^ 4) (by fl_num) (by fl_num) (by fl_num)
  have b4 := B32.add b3 cVT (e := 187 / 10 ^ 9) (R := 8775 / 10 ^ 4) (by fl_num) (by fl_num) (by fl_num)
  have b5 := B32.mul eV eT (e := 366 / 10 ^ 11) (R := 6130 / 10 ^ 5) (by fl_num) (by fl_num) (by fl_num)
  have b6 := B32.add eP b5 (e := 822 / 10 ^ 11) (R := 7650 / 10 ^ 5) (by fl_num) (by fl_num) (by fl_num)
  have b7 := B32.mul eH eA (e := 597 / 10 ^ 10) (R := 1001 / 10 ^ 3) (by fl_num) (by fl_num) (by fl_num)
  have b8 := B32.mul b7 csq (e := 112 / 10 ^ 10) (R := 6257 / 10 ^ 5) (by fl_num) (by fl_num) (by fl_num)
  have b9 := B32.add b6 b8 (e := 278 / 10 ^ 10) (R := 1391 / 10 ^ 4) (by fl_num) (by fl_num) (by fl_num)
  have b10 := B32.add b9 cPT (e := 452 / 10 ^ 10) (R := 1517 / 10 ^ 4) (by fl_num) (by fl_num) (by fl_num)
  refine ⟨(b1.1.congr (by node_eq)).mono (by norm_num),
    (b4.1.congr (by node_eq)).mono (by norm_num), (b10.1.congr (by node_eq)).mono (by norm_num)⟩

set_option maxHeartbeats 4000000 in
theorem fl_decr_S (hL : LibmSpec) {A0 V0 P0 tj Jm : Float32} (fA : A0.IsFinite) (fV : V0.IsFinite)
    (fP : P0.IsFinite) (ft : tj.IsFinite) (fJ : Jm.IsFinite) (ht0 : 1 / 300 ≤ tj.toReal)
    (ht1 : tj.toReal ≤ 1 / 4) (hJ : |Jm.toReal| ≤ 6) (hA : |A0.toReal| ≤ 2001 / 1000)
    (hV : |V0.toReal| ≤ 613 / 2500) (hP : |P0.toReal| ≤ 19 / 1250) :
    A32 (A0 - Jm * (0.5 : Float32) * tj + Jm * tj) (SC.decrNode ⟨A0.toReal, V0.toReal, P0.toReal⟩ Jm.toReal (Real.pi / tj.toReal) tj.toReal).a (597 / 1000000000) ∧
    A32 (V0 - vtF tj Jm + (A0 - Jm * (0.5 : Float32) * tj) * tj + Jm * sq_float tj) (SC.decrNode ⟨A0.toReal, V0.toReal, P0.toReal⟩ Jm.toReal (Real.pi / tj.toReal) tj.toReal).v (383 / 1000000000) ∧
    A32 (P0 - ptF tj Jm + (V0 - vtF tj Jm) * tj + (0.5 : Float32) * (A0 - Jm * (0.5 : Float32) * tj) * sq_float tj + p2tF tj Jm) (SC.decrNode ⟨A0.toReal, V0.toReal, P0.toReal⟩ Jm.toReal (Real.pi / tj.toReal) tj.toReal).p (69 / 500000000) := by
  obtain ⟨cAT, cVT, cPT, cA2T, cV2T, cP2T, csq⟩ := ramp_consts hL ft fJ ht0 ht1 hJ
  have eA := B32.of_exact fA hA
  have eV := B32.of_exact fV hV
  have eP := B32.of_exact fP hP
  have eT : B32 tj tj.toReal 0 (1 / 4) := B32.of_exact ft (by rw [abs_of_pos (by linarith)]; exact ht1)
  have eH : B32 (0.5 : Float32) (1 / 2) 0 (1 / 2) :=
    B32.sce_lit f32_isFinite_0p5 f32_toReal_0p5 (by norm_num)
  have b1 := B32.sub eA cAT (e := 254 / 10 ^ 9) (R := 2751 / 10 ^ 3) (by fl_num) (by fl_num) (by fl_num)
  have b2 := B32.add b1 cA2T (e := 597 / 10 ^ 9) (R := 4251 / 10 ^ 3) (by fl_num) (by fl_num) (by fl_num)
  have b3 := B32.sub eV cVT (e := 827 / 10 ^ 10) (R := 3772 / 10 ^ 4) (by fl_num) (by fl_num) (by fl_num)
  have b4 := B32.mul b1 eT (e := 105 / 10 ^ 9) (R := 6878 / 10 ^ 4) (by fl_num) (by fl_num) (by fl_num)
  have b5 := B32.add b3 b4 (e := 252 / 10 ^ 9) (R := 1065 / 10 ^ 3) (by fl_num) (by fl_num) (by fl_num)
  have b6 := B32.add b5 cV2T (e := 383 / 10 ^ 9) (R := 1440 / 10 ^ 3) (by fl_num) (by fl_num) (by fl_num)
  have b7 := B32.sub eP cPT (e := 992 / 10 ^ 11) (R := 2780 / 10 ^ 5) (by fl_num) (by fl_num) (by fl_num)
  have b8 := B32.mul b3 eT (e := 263 / 10 ^ 10) (R := 9430 / 10 ^ 5) (by fl_num) (by fl_num) (by fl_num)
  have b9 := B32.add b7 b8 (e := 435 / 10 ^ 10) (R := 1221 / 10 ^ 4) (by fl_num) (by fl_num) (by fl_num)
  have b10 := B32.mul eH b1 (e := 209 / 10 ^ 9) (R := 1376 / 10 ^ 3) (by fl_num) (by fl_num) (by fl_num)
  have b11 := B32.mul b10 csq (e := 234 / 10 ^ 10) (R := 8600 / 10 ^ 5) (by fl_num) (by fl_num) (by fl_num)
  have b12 := B32.add b9 b11 (e := 794 / 10 ^ 10) (R := 2081 / 10 ^ 4) (by fl_num) (by fl_num) (by fl_num)
  have b13 := B32.add b12 cP2T (e := 138 / 10 ^ 9) (R := 2802 / 10 ^ 4) (by fl_num) (by fl_num) (by fl_num)
  refine ⟨(b2.1.congr (by node_eq)).mono (by norm_num),
    (b6.1.congr (by node_eq)).mono (by norm_num), (b13.1.congr (by node_eq)).mono (by norm_num)⟩

set_option maxHeartbeats 4000000 in
theorem fl_constJ_G (hL : LibmSpec) {A0 V0 P0 tin J0 : Float32} (fA : A0.IsFinite) (fV : V0.IsFinite)
    (fP : P0.IsFinite) (ft : tin.IsFinite) (fJ : J0.IsFinite) (ht0 : 0 ≤ tin.toReal)
    (ht1 : tin.toReal ≤ 1 / 2) (hJ : |J0.toReal| ≤ 6) (hA : |A0.toReal| ≤ 2001 / 1000)
    (hV : |V0.toReal| ≤ 3001 / 1000) (hP : |P0.toReal| ≤ 4001 / 1000) :
    A32 (A0 + J0 * tin) (SC.constNode ⟨A0.toReal, V0.toReal, P0.toReal⟩ J0.toReal tin.toReal).a (239 / 500000000) ∧
    A32 (V0 + A0 * tin + (0.5 : Float32) * J0 * sq_float tin) (SC.constNode ⟨A0.toReal, V0.toReal, P0.toReal⟩ J0.toReal tin.toReal).v (359 / 500000000) ∧
    A32 (P0 + V0 * tin + (0.5 : Float32) * A0 * sq_float tin +
      (1.0 : Float32) / (6.0 : Float32) * J0 * Float32.pow tin (3.0 : Float32)) (SC.constNode ⟨A0.toReal, V0.toReal, P0.toReal⟩ J0.toReal tin.toReal).p (121 / 100000000) := by
  have pw := B32.pow3 hL ft ht0 ht1 (by norm_num)
  simp only [sq_float_eq]
  have eA := B32.of_exact fA hA
  have eV := B32.of_exact fV hV
  have eP := B32.of_exact fP hP
  have eJ := B32.of_exact fJ hJ
  have eT : B32 tin tin.toReal 0 (1 / 2) := B32.of_exact ft (by rw [abs_of_nonneg ht0]; exact ht1)
  have eH : B32 (0.5 : Float32) (1 / 2) 0 (1 / 2) :=
    B32.sce_lit f32_isFinite_0p5 f32_toReal_0p5 (by norm_num)
  have c16 : B32 ((1.0 : Float32) / (6.0 : Float32)) (1 / 6) (1 / 201326592) (1 / 6) := by
    rw [sce_c6]; exact ⟨⟨sce_isFinite_c6, by rw [sce_toReal_c6]; norm_num⟩, by norm_num⟩
  have b1 := B32.mul eJ eT (e := 179 / 10 ^ 9) (R := 3) (by fl_num) (by fl_num) (by fl_num)
  have b2 := B32.add eA b1 (e := 478 / 10 ^ 9) (R := 5001 / 10 ^ 3) (by fl_num) (by fl_num) (by fl_num)
  have b3 := B32.mul eA eT (e := 597 / 10 ^ 10) (R := 1001 / 10 ^ 3) (by fl_num) (by fl_num) (by fl_num)
  have b4 := B32.add eV b3 (e := 299 / 10 ^ 9) (R := 4002 / 10 ^ 3) (by fl_num) (by fl_num) (by fl_num)
  have b5 := B32.mul eH eJ (e := 179 / 10 ^ 9) (R := 3) (by fl_num) (by fl_num) (by fl_num)
  have b6 := B32.mul eT eT (e := 150 / 10 ^ 10) (R := 2500 / 10 ^ 4) (by fl_num) (by fl_num) (by fl_num)
  have b7 := B32.mul b5 b6 (e := 135 / 10 ^ 9) (R := 7500 / 10 ^ 4) (by fl_num) (by fl_num) (by fl_num)
  have b8 := B32.add b4 b7 (e := 718 / 10 ^ 9) (R := 4752 / 10 ^ 3) (by fl_num) (by fl_num) (by fl_num)
  have b9 := B32.mul eV eT (e := 895 / 10 ^ 10) (R := 1501 / 10 ^ 3) (by fl_num) (by fl_num) (by fl_num)
  have b10 := B32.add eP b9 (e := 418 / 10 ^ 9) (R := 5502 / 10 ^ 3) (by fl_num) (by fl_num) (by fl_num)
  have b11 := B32.mul eH eA (e := 597 / 10 ^ 10) (R := 1001 / 10 ^ 3) (by fl_num) (by fl_num) (by fl_num)
  have b12 := B32.mul b11 b6 (e := 449 / 10 ^ 10) (R := 2503 / 10 ^ 4) (by fl_num) (by fl_num) (by fl_num)
  have b13 := B32.add b10 b12 (e := 806 / 10 ^ 9) (R := 5753 / 10 ^ 3) (by fl_num) (by fl_num) (by fl_num)
  have b14 := B32.mul c16 eJ (e := 895 / 10 ^ 10) (R := 1) (by fl_num) (by fl_num) (by fl_num)
  have b15 := B32.mul b14 pw (e := 485 / 10 ^ 10) (R := 1250 / 10 ^ 4) (by fl_num) (by fl_num) (by fl_num)
  have b16 := B32.add b13 b15 (e := 121 / 10 ^ 8) (R := 5878 / 10 ^ 3) (by fl_num) (by fl_num) (by fl_num)
  refine ⟨(b2.1.congr (by node_eq)).mono (by norm_num),
    (b8.1.congr (by node_eq)).mono (by norm_num), (b16.1.congr (by node_eq)).mono (by norm_num)⟩

set_option maxHeartbeats 4000000 in
theorem fl_const0_G (hL : LibmSpec) {A0 V0 P0 tin : Float32} (fA : A0.IsFinite) (fV : V0.IsFinite)
    (fP : P0.IsFinite) (ft : tin.IsFinite) (ht0 : 0 ≤ tin.toReal)
    (ht1 : tin.toReal ≤ 3) (hA : |A0.toReal| ≤ 2001 / 1000)
    (hV : |V0.toReal| ≤ 3001 / 1000) (hP : |P0.toReal| ≤ 4001 / 1000) :
    A32 (A0 + (0.0 : Float32) * tin) (SC.constNode ⟨A0.toReal, V0.toReal, P0.toReal⟩ 0 tin.toReal).a 0 ∧
    A32 (V0 + A0 * tin + (0.5 : Float32) * (0.0 : Float32) * sq_float tin) (SC.constNode ⟨A0.toReal, V0.toReal, P0.toReal⟩ 0 tin.toReal).v (179 / 200000000) ∧
    A32 (P0 + V0 * tin + (0.5 : Float32) * A0 * sq_float tin +
      (1.0 : Float32) / (6.0 : Float32) * (0.0 : Float32) * Float32.pow tin (3.0 : Float32)) (SC.constNode ⟨A0.toReal, V0.toReal, P0.toReal⟩ 0 tin.toReal).p
      (213 / 50000000) := by
  have pw := B32.pow3 hL ft ht0 ht1 (by norm_num)
  simp only [sq_float_eq]
  have eA := B32.of_exact fA hA
  have eV := B32.of_exact fV hV
  have eP := B32.of_exact fP hP
  have eT : B32 tin tin.toReal 0 (3) := B32.of_exact ft (by rw [abs_of_nonneg ht0]; exact ht1)
  have eH : B32 (0.5 : Float32) (1 / 2) 0 (1 / 2) :=
    B32.sce_lit f32_isFinite_0p5 f32_toReal_0p5 (by norm_num)
  have z1 := zero_mul_val ft f32_isFinite_0p0 f32_toReal_0p0
  have z2 := Float32.mul_zero_val f32_isFinite_0p5 f32_isFinite_0p0 f32_toReal_0p0
  have z3 := zero_mul_val (Float32.mul_err_all ft ft (by
    have := Float32.abs_toReal_le_maxFinite tin
    have h2 : |tin.toReal * tin.toReal| ≤ 3 * 3 := by
      rw [abs_mul, abs_of_nonneg ht0]; exact mul_le_mul ht1 ht1 ht0 (by norm_num)
    linarith [capF_le_max32, show (3 : ℝ) * 3 ≤ capF by norm_num [capF]])).1 z2.1 z2.2
  have z4 := Float32.mul_zero_val (a := (1.0 : Float32) / (6.0 : Float32))
    (by rw [sce_c6]; exact sce_isFinite_c6) f32_isFinite_0p0 f32_toReal_0p0
  have z5 := zero_mul_val pw.1.1 z4.1 z4.2
  have eA' : A32 (A0 + (0.0 : Float32) * tin) A0.toReal 0 :=
    ⟨(Float32.add_zero_val fA z1.1 z1.2).1, by rw [(Float32.add_zero_val fA z1.1 z1.2).2]; simp⟩
  have b1 := B32.mul eA eT (e := 358 / 10 ^ 9) (R := 6003 / 10 ^ 3) (by fl_num) (by fl_num) (by fl_num)
  have b2 := B32.add eV b1 (e := 895 / 10 ^ 9) (R := 9004 / 10 ^ 3) (by fl_num) (by fl_num) (by fl_num)
  have b3 := B32.mul eV eT (e := 537 / 10 ^ 9) (R := 9003 / 10 ^ 3) (by fl_num) (by fl_num) (by fl_num)
  have b4 := B32.add eP b3 (e := 132 / 10 ^ 8) (R := 1301 / 10 ^ 2) (by fl_num) (by fl_num) (by fl_num)
  have b5 := B32.mul eH eA (e := 597 / 10 ^ 10) (R := 1001 / 10 ^ 3) (by fl_num) (by fl_num) (by fl_num)
  have b6 := B32.mul eT eT (e := 537 / 10 ^ 9) (R := 9) (by fl_num) (by fl_num) (by fl_num)
  have b7 := B32.mul b5 b6 (e := 162 / 10 ^ 8) (R := 9009 / 10 ^ 3) (by fl_num) (by fl_num) (by fl_num)
  have b8 := B32.add b4 b7 (e := 426 / 10 ^ 8) (R := 2202 / 10 ^ 2) (by fl_num) (by fl_num) (by fl_num)
  have hV' := B32.add_zero' b2 z3.1 z3.2
  have hP' := B32.add_zero' b8 z5.1 z5.2
  refine ⟨eA'.congr (by node_eq),
    (hV'.1.congr (by node_eq)).mono (by norm_num), (hP'.1.congr (by node_eq)).mono (by norm_num)⟩

set_option maxHeartbeats 4000000 in
theorem fl_constJ_S (hL : LibmSpec) {A0 V0 P0 tin J0 : Float32} (fA : A0.IsFinite) (fV : V0.IsFinite)
    (fP : P0.IsFinite) (ft : tin.IsFinite) (fJ : J0.IsFinite) (ht0 : 0 ≤ tin.toReal)
    (ht1 : tin.toReal ≤ 1 / 2) (hJ : |J0.toReal| ≤ 6) (hA : |A0.toReal| ≤ 2001 / 1000)
    (hV : |V0.toReal| ≤ 613 / 2500) (hP : |P0.toReal| ≤ 19 / 1250) :
    A32 (A0 + J0 * tin) (SC.constNode ⟨A0.toReal, V0.toReal, P0.toReal⟩ J0.toReal tin.toReal).a (239 / 500000000) ∧
    A32 (V0 + A0 * tin + (0.5 : Float32) * J0 * sq_float tin) (SC.constNode ⟨A0.toReal, V0.toReal, P0.toReal⟩ J0.toReal tin.toReal).v (39 / 100000000) ∧
    A32 (P0 + V0 * tin + (0.5 : Float32) * A0 * sq_float tin +
      (1.0 : Float32) / (6.0 : Float32) * J0 * Float32.pow tin (3.0 : Float32)) (SC.constNode ⟨A0.toReal, V0.toReal, P0.toReal⟩ J0.toReal tin.toReal).p (163 / 1000000000) := by
  have pw := B32.pow3 hL ft ht0 ht1 (by norm_num)
  simp only [sq_float_eq]
  have eA := B32.of_exact fA hA
  have eV := B32.of_exact fV hV
  have eP := B32.of_exact fP hP
  have eJ := B32.of_exact fJ hJ
  have eT : B32 tin tin.toReal 0 (1 / 2) := B32.of_exact ft (by rw [abs_of_nonneg ht0]; exact ht1)
  have eH : B32 (0.5 : Float32) (1 / 2) 0 (1 / 2) :=
    B32.sce_lit f32_isFinite_0p5 f32_toReal_0p5 (by norm_num)
  have c16 : B32 ((1.0 : Float32) / (6.0 : Float32)) (1 / 6) (1 / 201326592) (1 / 6) := by
    rw [sce_c6]; exact ⟨⟨sce_isFinite_c6, by rw [sce_toReal_c6]; norm_num⟩, by norm_num⟩
  have b1 := B32.mul eJ eT (e := 179 / 10 ^ 9) (R := 3) (by fl_num) (by fl_num) (by fl_num)
  have b2 := B32.add eA b1 (e := 478 / 10 ^ 9) (R := 5001 / 10 ^ 3) (by fl_num) (by fl_num) (by fl_num)
  have b3 := B32.mul eA eT (e := 597 / 10 ^ 10) (R := 1001 / 10 ^ 3) (by fl_num) (by fl_num) (by fl_num)
  have b4 := B32.add eV b3 (e := 135 / 10 ^ 9) (R := 1247 / 10 ^ 3) (by fl_num) (by fl_num) (by fl_num)
  have b5 := B32.mul eH eJ (e := 179 / 10 ^ 9) (R := 3) (by fl_num) (by fl_num) (by fl_num)
  have b6 := B32.mul eT eT (e := 150 / 10 ^ 10) (R := 2500 / 10 ^ 4) (by fl_num) (by fl_num) (by fl_num)
  have b7 := B32.mul b5 b6 (e := 135 / 10 ^ 9) (R := 7500 / 10 ^ 4) (by fl_num) (by fl_num) (by fl_num)
  have b8 := B32.add b4 b7 (e := 390 / 10 ^ 9) (R := 1997 / 10 ^ 3) (by fl_num) (by fl_num) (by fl_num)
  have b9 := B32.mul eV eT (e := 731 / 10 ^ 11) (R := 1226 / 10 ^ 4) (by fl_num) (by fl_num) (by fl_num)
  have b10 := B32.add eP b9 (e := 156 / 10 ^ 10) (R := 1378 / 10 ^ 4) (by fl_num) (by fl_num) (by fl_num)
  have b11 := B32.mul eH eA (e := 597 / 10 ^ 10) (R := 1001 / 10 ^ 3) (by fl_num) (by fl_num) (by fl_num)
  have b12 := B32.mul b11 b6 (e := 449 / 10 ^ 10) (R := 2503 / 10 ^ 4) (by fl_num) (by fl_num) (by fl_num)
  have b13 := B32.add b10 b12 (e := 837 / 10 ^ 10) (R := 3881 / 10 ^ 4) (by fl_num) (by fl_num) (by fl_num)
  have b14 := B32.mul c16 eJ (e := 895 / 10 ^ 10) (R := 1) (by fl_num) (by fl_num) (by fl_num)
  have b15 := B32.mul b14 pw (e := 485 / 10 ^ 10) (R := 1250 / 10 ^ 4) (by fl_num) (by fl_num) (by fl_num)
  have b16 := B32.add b13 b15 (e := 163 / 10 ^ 9) (R := 5131 / 10 ^ 4) (by fl_num) (by fl_num) (by fl_num)
  refine ⟨(b2.1.congr (by node_eq)).mono (by norm_num),
    (b8.1.congr (by node_eq)).mono (by norm_num), (b16.1.congr (by node_eq)).mono (by norm_num)⟩

set_option maxHeartbeats 4000000 in
theorem fl_const0_S (hL : LibmSpec) {A0 V0 P0 tin : Float32} (fA : A0.IsFinite) (fV : V0.IsFinite)
    (fP : P0.IsFinite) (ft : tin.IsFinite) (ht0 : 0 ≤ tin.toReal)
    (ht1 : tin.toReal ≤ 3) (hA : |A0.toReal| ≤ 2001 / 1000)
    (hV : |V0.toReal| ≤ 613 / 2500) (hP : |P0.toReal| ≤ 19 / 1250) :
    A32 (A0 + (0.0 : Float32) * tin) (SC.constNode ⟨A0.toReal, V0.toReal, P0.toReal⟩ 0 tin.toReal).a 0 ∧
    A32 (V0 + A0 * tin + (0.5 : Float32) * (0.0 : Float32) * sq_float tin) (SC.constNode ⟨A0.toReal, V0.toReal, P0.toReal⟩ 0 tin.toReal).v (731 / 1000000000) ∧
    A32 (P0 + V0 * tin + (0.5 : Float32) * A0 * sq_float tin +
      (1.0 : Float32) / (6.0 : Float32) * (0.0 : Float32) * Float32.pow tin (3.0 : Float32)) (SC.constNode ⟨A0.toReal, V0.toReal, P0.toReal⟩ 0 tin.toReal).p
      (23 / 10000000) := by
  have pw := B32.pow3 hL ft ht0 ht1 (by norm_num)
  simp only [sq_float_eq]
  have eA := B32.of_exact fA hA
  have eV := B32.of_exact fV hV
  have eP := B32.of_exact fP hP
  have eT : B32 tin tin.toReal 0 (3) := B32.of_exact ft (by rw [abs_of_nonneg ht0]; exact ht1)
  have eH : B32 (0.5 : Float32) (1 / 2) 0 (1 / 2) :=
    B32.sce_lit f32_isFinite_0p5 f32_toReal_0p5 (by norm_num)
  have z1 := zero_mul_val ft f32_isFinite_0p0 f32_toReal_0p0
  have z2 := Float32.mul_zero_val f32_isFinite_0p5 f32_isFinite_0p0 f32_toReal_0p0
  have z3 := zero_mul_val (Float32.mul_err_all ft ft (by
    have := Float32.abs_toReal_le_maxFinite tin
    have h2 : |tin.toReal * tin.toReal| ≤ 3 * 3 := by
      rw [abs_mul, abs_of_nonneg ht0]; exact mul_le_mul ht1 ht1 ht0 (by norm_num)
    linarith [capF_le_max32, show (3 : ℝ) * 3 ≤ capF by norm_num [capF]])).1 z2.1 z2.2
  have z4 := Float32.mul_zero_val (a := (1.0 : Float32) / (6.0 : Float32))
    (by rw [sce_c6]; exact sce_isFinite_c6) f32_isFinite_0p0 f32_toReal_0p0
  have z5 := zero_mul_val pw.1.1 z4.1 z4.2
  have eA' : A32 (A0 + (0.0 : Float32) * tin) A0.toReal 0 :=
    ⟨(Float32.add_zero_val fA z1.1 z1.2).1, by rw [(Float32.add_zero_val fA z1.1 z1.2).2]; simp⟩
  have b1 := B32.mul eA eT (e := 358 / 10 ^ 9) (R := 6003 / 10 ^ 3) (by fl_num) (by fl_num) (by fl_num)
  have b2 := B32.add eV b1 (e := 731 / 10 ^ 9) (R := 6249 / 10 ^ 3) (by fl_num) (by fl_num) (by fl_num)
  have b3 := B32.mul eV eT (e := 439 / 10 ^ 10) (R := 7356 / 10 ^ 4) (by fl_num) (by fl_num) (by fl_num)
  have b4 := B32.add eP b3 (e := 887 / 10 ^ 10) (R := 7508 / 10 ^ 4) (by fl_num) (by fl_num) (by fl_num)
  have b5 := B32.mul eH eA (e := 597 / 10 ^ 10) (R := 1001 / 10 ^ 3) (by fl_num) (by fl_num) (by fl_num)
  have b6 := B32.mul eT eT (e := 537 / 10 ^ 9) (R := 9) (by fl_num) (by fl_num) (by fl_num)
  have b7 := B32.mul b5 b6 (e := 162 / 10 ^ 8) (R := 9009 / 10 ^ 3) (by fl_num) (by fl_num) (by fl_num)
  have b8 := B32.add b4 b7 (e := 230 / 10 ^ 8) (R := 9760 / 10 ^ 3) (by fl_num) (by fl_num) (by fl_num)
  have hV' := B32.add_zero' b2 z3.1 z3.2
  have hP' := B32.add_zero' b8 z5.1 z5.2
  refine ⟨eA'.congr (by node_eq),
    (hV'.1.congr (by node_eq)).mono (by norm_num), (hP'.1.congr (by node_eq)).mono (by norm_num)⟩

set_option maxHeartbeats 4000000 in
theorem fl_const15 (hL : LibmSpec) {A0 V0 P0 tin : Float32} (fA : A0.IsFinite) (fV : V0.IsFinite)
    (fP : P0.IsFinite) (ft : tin.IsFinite) (ht0 : 0 ≤ tin.toReal)
    (ht1 : tin.toReal ≤ 15) (hA : |A0.toReal| ≤ 0)
    (hV : |V0.toReal| ≤ 3001 / 1000) (hP : |P0.toReal| ≤ 4001 / 1000) :
    A32 (A0 + (0.0 : Float32) * tin) (SC.constNode ⟨A0.toReal, V0.toReal, P0.toReal⟩ 0 tin.toReal).a 0 ∧
    A32 (V0 + A0 * tin + (0.5 : Float32) * (0.0 : Float32) * sq_float tin) (SC.constNode ⟨A0.toReal, V0.toReal, P0.toReal⟩ 0 tin.toReal).v (179 / 1000000000) ∧
    A32 (P0 + V0 * tin + (0.5 : Float32) * A0 * sq_float tin +
      (1.0 : Float32) / (6.0 : Float32) * (0.0 : Float32) * Float32.pow tin (3.0 : Float32)) (SC.constNode ⟨A0.toReal, V0.toReal, P0.toReal⟩ 0 tin.toReal).p
      (171 / 20000000) := by
  have pw := B32.pow3 hL ft ht0 ht1 (by norm_num)
  simp only [sq_float_eq]
  have eA := B32.of_exact fA hA
  have eV := B32.of_exact fV hV
  have eP := B32.of_exact fP hP
  have eT : B32 tin tin.toReal 0 (15) := B32.of_exact ft (by rw [abs_of_nonneg ht0]; exact ht1)
  have eH : B32 (0.5 : Float32) (1 / 2) 0 (1 / 2) :=
    B32.sce_lit f32_isFinite_0p5 f32_toReal_0p5 (by norm_num)
  have z1 := zero_mul_val ft f32_isFinite_0p0 f32_toReal_0p0
  have z2 := Float32.mul_zero_val f32_isFinite_0p5 f32_isFinite_0p0 f32_toReal_0p0
  have z3 := zero_mul_val (Float32.mul_err_all ft ft (by
    have := Float32.abs_toReal_le_maxFinite tin
    have h2 : |tin.toReal * tin.toReal| ≤ 15 * 15 := by
      rw [abs_mul, abs_of_nonneg ht0]; exact mul_le_mul ht1 ht1 ht0 (by norm_num)
    linarith [capF_le_max32, show (15 : ℝ) * 15 ≤ capF by norm_num [capF]])).1 z2.1 z2.2
  have z4 := Float32.mul_zero_val (a := (1.0 : Float32) / (6.0 : Float32))
    (by rw [sce_c6]; exact sce_isFinite_c6) f32_isFinite_0p0 f32_toReal_0p0
  have z5 := zero_mul_val pw.1.1 z4.1 z4.2
  have eA' : A32 (A0 + (0.0 : Float32) * tin) A0.toReal 0 :=
    ⟨(Float32.add_zero_val fA z1.1 z1.2).1, by rw [(Float32.add_zero_val fA z1.1 z1.2).2]; simp⟩
  have b1 := B32.mul eA eT (e := 100 / 10 ^ 42) (R := 0) (by fl_num) (by fl_num) (by fl_num)
  have b2 := B32.add eV b1 (e := 179 / 10 ^ 9) (R := 3001 / 10 ^ 3) (by fl_num) (by fl_num) (by fl_num)
  have b3 := B32.mul eV eT (e := 269 / 10 ^ 8) (R := 4502 / 10 ^ 2) (by fl_num) (by fl_num) (by fl_num)
  have b4 := B32.add eP b3 (e := 562 / 10 ^ 8) (R := 4903 / 10 ^ 2) (by fl_num) (by fl_num) (by fl_num)
  have b5 := B32.mul eH eA (e := 100 / 10 ^ 42) (R := 0) (by fl_num) (by fl_num) (by fl_num)
  have b6 := B32.mul eT eT (e := 135 / 10 ^ 7) (R := 225) (by fl_num) (by fl_num) (by fl_num)
  have b7 := B32.mul b5 b6 (e := 227 / 10 ^ 40) (R := 0) (by fl_num) (by fl_num) (by fl_num)
  have b8 := B32.add b4 b7 (e := 855 / 10 ^ 8) (R := 4903 / 10 ^ 2) (by fl_num) (by fl_num) (by fl_num)
  have hV' := B32.add_zero' b2 z3.1 z3.2
  have hP' := B32.add_zero' b8 z5.1 z5.2
  refine ⟨eA'.congr (by node_eq),
    (hV'.1.congr (by node_eq)).mono (by norm_num), (hP'.1.congr (by node_eq)).mono (by norm_num)⟩

end SCT

end

end Contracts.Mission
