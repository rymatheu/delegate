import Contracts.Mission.SCurveTableNear
import Contracts.Mission.SCurveTableReal

/-!
# The `add_segments` table: error chains

Generated chains of `Near` steps through the table, with numeric error bounds.
-/

namespace Contracts.Mission

open Float.Model UnpackedFloat AC_WPNav_lib

noncomputable section

namespace SCT

set_option maxHeartbeats 8000000 in
/-- **The accelerating phase**, regime `G`. -/
theorem accel_G (hL : LibmSpec) {L Jm tj t2 t4 : Float32} {E : ℕ → SCurve.segment_t}
    (hEs : ∀ k, E (k + 1) = stepE L Jm tj t2 t4 t2 k (E k))
    (h0 : Near (E 0) 0 ⟨0, 0, 0⟩ 0 0 0 0)
    (fJ : Jm.IsFinite) (ft : tj.IsFinite) (ft2 : t2.IsFinite) (ft4 : t4.IsFinite)
    {t15 : ℝ} (hP : SC.ProfIn Jm.toReal tj.toReal (eff t2.toReal) (eff t4.toReal) t15)
    (hV7 : (SC.node Jm.toReal tj.toReal (eff t2.toReal) (eff t4.toReal) t15 7).v ≤ 3) (hP7 : (SC.node Jm.toReal tj.toReal (eff t2.toReal) (eff t4.toReal) t15 7).p ≤ 2) :
    Near (E 1) (SC.tEnd Jm.toReal tj.toReal (eff t2.toReal) (eff t4.toReal) t15 1) (SC.node Jm.toReal tj.toReal (eff t2.toReal) (eff t4.toReal) t15 1) (299 / 1000000000) (127 / 500000000) (129 / 250000000) (37 / 40000000) ∧
    Near (E 2) (SC.tEnd Jm.toReal tj.toReal (eff t2.toReal) (eff t4.toReal) t15 2) (SC.node Jm.toReal tj.toReal (eff t2.toReal) (eff t4.toReal) t15 2) (299 / 500000000) (183 / 250000000) (137 / 100000000) (243 / 100000000) ∧
    Near (E 3) (SC.tEnd Jm.toReal tj.toReal (eff t2.toReal) (eff t4.toReal) t15 3) (SC.node Jm.toReal tj.toReal (eff t2.toReal) (eff t4.toReal) t15 3) (897 / 1000000000) (133 / 100000000) (243 / 100000000) (41 / 10000000) ∧
    Near (E 4) (SC.tEnd Jm.toReal tj.toReal (eff t2.toReal) (eff t4.toReal) t15 4) (SC.node Jm.toReal tj.toReal (eff t2.toReal) (eff t4.toReal) t15 4) (3 / 2500000) (133 / 100000000) (183 / 25000000) (217 / 10000000) ∧
    Near (E 5) (SC.tEnd Jm.toReal tj.toReal (eff t2.toReal) (eff t4.toReal) t15 5) (SC.node Jm.toReal tj.toReal (eff t2.toReal) (eff t4.toReal) t15 5) (3 / 2000000) (159 / 100000000) (817 / 100000000) (49 / 2000000) ∧
    Near (E 6) (SC.tEnd Jm.toReal tj.toReal (eff t2.toReal) (eff t4.toReal) t15 6) (SC.node Jm.toReal tj.toReal (eff t2.toReal) (eff t4.toReal) t15 6) (9 / 5000000) (207 / 100000000) (969 / 100000000) (3 / 100000) ∧
    Near (E 7) (SC.tEnd Jm.toReal tj.toReal (eff t2.toReal) (eff t4.toReal) t15 7) (SC.node Jm.toReal tj.toReal (eff t2.toReal) (eff t4.toReal) t15 7) (21 / 10000000) (0) (111 / 10000000) (169 / 5000000) := by
  set N := SC.node Jm.toReal tj.toReal (eff t2.toReal) (eff t4.toReal) t15 with hN
  set tE := SC.tEnd Jm.toReal tj.toReal (eff t2.toReal) (eff t4.toReal) t15 with htE
  have hJ : |Jm.toReal| ≤ 6 := abs_le.2 ⟨by linarith [hP.J0], hP.J1⟩
  have fJn : (-Jm).IsFinite := (Float32.isFinite_neg _).2 fJ
  have hJn : |(-Jm).toReal| ≤ 6 := by rw [Float32.toReal_neg, abs_neg]; exact hJ
  have htj0 := hP.tj0
  have htj1 := hP.tj1
  have hpos : is_positive_float tj = true := sce_isPos ft (by linarith)
  have nb : ∀ k ≤ 22, |(N k).a| ≤ 2 ∧ 0 ≤ (N k).v ∧ (N k).v ≤ 3 := fun k hk => SC.node_bounds hP hk
  have pb : ∀ k ≤ 7, 0 ≤ (N k).p ∧ (N k).p ≤ 2 := fun k hk =>
    ⟨SC.pos_nonneg hP (by omega), (SC.pos_mono' hP hk (by norm_num)).trans hP7⟩
  have vb : ∀ k ≤ 7, 0 ≤ (N k).v ∧ (N k).v ≤ 3 := fun k hk =>
    ⟨(nb k (by omega)).2.1, (SC.vel_le7 hP hk).trans hV7⟩
  have tb : ∀ k ≤ 14, 0 ≤ tE k ∧ tE k ≤ 5 := fun k hk =>
    ⟨SC.tEnd_nonneg hP k, (SC.tEnd_le hP).1 k hk⟩
  have aL : (N 7).a = 0 := (SC.node_a (Jm := Jm.toReal) (tj := tj.toReal) (t2 := eff t2.toReal)
    (t4 := eff t4.toReal) (t15 := t15)).2.2.2.2.2.2.1
  have s0 : Near (E 0) (tE 0) (N 0) 0 0 0 0 := h0
  have s1 : Near (E 1) (tE 1) (N 1) (299 / 1000000000) (127 / 500000000) (129 / 250000000) (37 / 40000000) := by
    have ee : E 1 = incrE (E 0) tj Jm := by rw [hEs]; rfl
    have ne : N 1 = SC.incrNode (N 0) (Jm.toReal) (Real.pi / tj.toReal) tj.toReal := rfl
    have te : tE 1 = tE 0 + tj.toReal := rfl
    have tt := tb 1 (by norm_num)
    rw [te] at tt
    have h := near_incr (TM := 5) (AM := 2001 / 1000) (VM := 3001 / 1000) (PM := 4001 / 1000) s0 hpos ft
      (by linarith) htj1 (mag_t tt.1 tt.2 le_rfl) (by norm_num) (by norm_num) (mag_a (nb 0 (by norm_num)).1 (by norm_num)) (mag_v (vb 0 (by norm_num)).1 (vb 0 (by norm_num)).2 (by norm_num)) (mag_v (pb 0 (by norm_num)).1 (pb 0 (by norm_num)).2 (by norm_num))
      (fun a b c => fl_incr_G hL s0.fin.2.1 s0.fin.2.2.1 s0.fin.2.2.2 ft fJ htj0 htj1 hJ a b c)
    rw [ee, ne, te]
    exact h.mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s2 : Near (E 2) (tE 2) (N 2) (299 / 500000000) (183 / 250000000) (137 / 100000000) (243 / 100000000) := by
    have ee : E 2 = constE (E 1) t2 Jm := by rw [hEs]; rfl
    have ne : N 2 = SC.constNode (N 1) (Jm.toReal) (eff t2.toReal) := rfl
    have te : tE 2 = tE 1 + eff t2.toReal := rfl
    have tt := tb 2 (by norm_num)
    rw [ee, ne, te]
    rw [te] at tt
    rcases Bool.eq_false_or_eq_true (is_positive_float t2) with hp | hp
    · have he := eff_pos ft2 hp
      rw [he.1] at tt ⊢
      have h := near_const (D := 1 / 2) (TM := 5) (AM := 2001 / 1000) (VM := 3001 / 1000) (PM := 4001 / 1000) s1 hp ft2
        (by linarith) (by rw [← he.1]; exact hP.t21) (mag_t tt.1 tt.2 le_rfl) (by norm_num) (by norm_num) (mag_a (nb 1 (by norm_num)).1 (by norm_num)) (mag_v (vb 1 (by norm_num)).1 (vb 1 (by norm_num)).2 (by norm_num)) (mag_v (pb 1 (by norm_num)).1 (pb 1 (by norm_num)).2 (by norm_num))
        (fun a b c => fl_constJ_G hL s1.fin.2.1 s1.fin.2.2.1 s1.fin.2.2.2 ft2 fJ (by linarith) (by rw [← he.1]; exact hP.t21) hJ a b c)
      exact h.mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · have he := eff_neg ft2 hp
      rw [he.1]
      exact (near_gated s1 hp _).mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s3 : Near (E 3) (tE 3) (N 3) (897 / 1000000000) (133 / 100000000) (243 / 100000000) (41 / 10000000) := by
    have ee : E 3 = decrE (E 2) tj Jm := by rw [hEs]; rfl
    have ne : N 3 = SC.decrNode (N 2) (Jm.toReal) (Real.pi / tj.toReal) tj.toReal := rfl
    have te : tE 3 = tE 2 + tj.toReal := rfl
    have tt := tb 3 (by norm_num)
    rw [te] at tt
    have h := near_decr (TM := 5) (AM := 2001 / 1000) (VM := 3001 / 1000) (PM := 4001 / 1000) s2 hpos ft
      (by linarith) htj1 (mag_t tt.1 tt.2 le_rfl) (by norm_num) (by norm_num) (mag_a (nb 2 (by norm_num)).1 (by norm_num)) (mag_v (vb 2 (by norm_num)).1 (vb 2 (by norm_num)).2 (by norm_num)) (mag_v (pb 2 (by norm_num)).1 (pb 2 (by norm_num)).2 (by norm_num))
      (fun a b c => fl_decr_G hL s2.fin.2.1 s2.fin.2.2.1 s2.fin.2.2.2 ft fJ htj0 htj1 hJ a b c)
    rw [ee, ne, te]
    exact h.mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s4 : Near (E 4) (tE 4) (N 4) (3 / 2500000) (133 / 100000000) (183 / 25000000) (217 / 10000000) := by
    have ee : E 4 = constE (E 3) t4 0.0 := by rw [hEs]; rfl
    have ne : N 4 = SC.constNode (N 3) (0) (eff t4.toReal) := rfl
    have te : tE 4 = tE 3 + eff t4.toReal := rfl
    have tt := tb 4 (by norm_num)
    rw [ee, ne, te]
    rw [te] at tt
    rcases Bool.eq_false_or_eq_true (is_positive_float t4) with hp | hp
    · have he := eff_pos ft4 hp
      rw [he.1] at tt ⊢
      have h := near_const0 (D := 3) (TM := 5) (AM := 2001 / 1000) (VM := 3001 / 1000) (PM := 4001 / 1000) s3 hp ft4
        (by linarith) (by rw [← he.1]; exact hP.t41) (mag_t tt.1 tt.2 le_rfl) (by norm_num) (by norm_num) (mag_a (nb 3 (by norm_num)).1 (by norm_num)) (mag_v (vb 3 (by norm_num)).1 (vb 3 (by norm_num)).2 (by norm_num)) (mag_v (pb 3 (by norm_num)).1 (pb 3 (by norm_num)).2 (by norm_num))
        (fun a b c => fl_const0_G hL s3.fin.2.1 s3.fin.2.2.1 s3.fin.2.2.2 ft4 (by linarith) (by rw [← he.1]; exact hP.t41) a b c)
      exact h.mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · have he := eff_neg ft4 hp
      rw [he.1]
      exact (near_gated s3 hp _).mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s5 : Near (E 5) (tE 5) (N 5) (3 / 2000000) (159 / 100000000) (817 / 100000000) (49 / 2000000) := by
    have ee : E 5 = incrE (E 4) tj (-Jm) := by rw [hEs]; rfl
    have ne : N 5 = SC.incrNode (N 4) (-Jm.toReal) (Real.pi / tj.toReal) tj.toReal := rfl
    have te : tE 5 = tE 4 + tj.toReal := rfl
    have tt := tb 5 (by norm_num)
    rw [te] at tt
    have h := near_incr (TM := 5) (AM := 2001 / 1000) (VM := 3001 / 1000) (PM := 4001 / 1000) s4 hpos ft
      (by linarith) htj1 (mag_t tt.1 tt.2 le_rfl) (by norm_num) (by norm_num) (mag_a (nb 4 (by norm_num)).1 (by norm_num)) (mag_v (vb 4 (by norm_num)).1 (vb 4 (by norm_num)).2 (by norm_num)) (mag_v (pb 4 (by norm_num)).1 (pb 4 (by norm_num)).2 (by norm_num))
      (fun a b c => fl_incr_G hL s4.fin.2.1 s4.fin.2.2.1 s4.fin.2.2.2 ft fJn htj0 htj1 hJn a b c)
    rw [Float32.toReal_neg] at h
    rw [ee, ne, te]
    exact h.mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s6 : Near (E 6) (tE 6) (N 6) (9 / 5000000) (207 / 100000000) (969 / 100000000) (3 / 100000) := by
    have ee : E 6 = constE (E 5) t2 (-Jm) := by rw [hEs]; rfl
    have ne : N 6 = SC.constNode (N 5) (-Jm.toReal) (eff t2.toReal) := rfl
    have te : tE 6 = tE 5 + eff t2.toReal := rfl
    have tt := tb 6 (by norm_num)
    rw [ee, ne, te]
    rw [te] at tt
    rcases Bool.eq_false_or_eq_true (is_positive_float t2) with hp | hp
    · have he := eff_pos ft2 hp
      rw [he.1] at tt ⊢
      have h := near_const (D := 1 / 2) (TM := 5) (AM := 2001 / 1000) (VM := 3001 / 1000) (PM := 4001 / 1000) s5 hp ft2
        (by linarith) (by rw [← he.1]; exact hP.t21) (mag_t tt.1 tt.2 le_rfl) (by norm_num) (by norm_num) (mag_a (nb 5 (by norm_num)).1 (by norm_num)) (mag_v (vb 5 (by norm_num)).1 (vb 5 (by norm_num)).2 (by norm_num)) (mag_v (pb 5 (by norm_num)).1 (pb 5 (by norm_num)).2 (by norm_num))
        (fun a b c => fl_constJ_G hL s5.fin.2.1 s5.fin.2.2.1 s5.fin.2.2.2 ft2 fJn (by linarith) (by rw [← he.1]; exact hP.t21) hJn a b c)
      rw [Float32.toReal_neg] at h
      exact h.mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · have he := eff_neg ft2 hp
      rw [he.1]
      exact (near_gated s5 hp _).mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s7 : Near (E 7) (tE 7) (N 7) (21 / 10000000) (0) (111 / 10000000) (169 / 5000000) := by
    have ee : E 7 = { decrE (E 6) tj (-Jm) with end_accel := 0.0 } := by rw [hEs]; rfl
    have ne : N 7 = SC.decrNode (N 6) (-Jm.toReal) (Real.pi / tj.toReal) tj.toReal := rfl
    have te : tE 7 = tE 6 + tj.toReal := rfl
    have tt := tb 7 (by norm_num)
    rw [te] at tt
    have h := near_decr (TM := 5) (AM := 2001 / 1000) (VM := 3001 / 1000) (PM := 4001 / 1000) s6 hpos ft
      (by linarith) htj1 (mag_t tt.1 tt.2 le_rfl) (by norm_num) (by norm_num) (mag_a (nb 6 (by norm_num)).1 (by norm_num)) (mag_v (vb 6 (by norm_num)).1 (vb 6 (by norm_num)).2 (by norm_num)) (mag_v (pb 6 (by norm_num)).1 (pb 6 (by norm_num)).2 (by norm_num))
      (fun a b c => fl_decr_G hL s6.fin.2.1 s6.fin.2.2.1 s6.fin.2.2.2 ft fJn htj0 htj1 hJn a b c)
    rw [Float32.toReal_neg] at h
    rw [ee, ne, te]
    rw [← ne] at h ⊢
    exact (h.zeroA aL).mono (by norm_num) le_rfl (by norm_num) (by norm_num)
  exact ⟨s1, s2, s3, s4, s5, s6, s7⟩

set_option maxHeartbeats 8000000 in
/-- **The accelerating phase**, regime `S`. -/
theorem accel_S (hL : LibmSpec) {L Jm tj t2 t4 : Float32} {E : ℕ → SCurve.segment_t}
    (hEs : ∀ k, E (k + 1) = stepE L Jm tj t2 t4 t2 k (E k))
    (h0 : Near (E 0) 0 ⟨0, 0, 0⟩ 0 0 0 0)
    (fJ : Jm.IsFinite) (ft : tj.IsFinite) (ft2 : t2.IsFinite) (ft4 : t4.IsFinite)
    {t15 : ℝ} (hP : SC.ProfIn Jm.toReal tj.toReal (eff t2.toReal) (eff t4.toReal) t15)
    (hV7 : (SC.node Jm.toReal tj.toReal (eff t2.toReal) (eff t4.toReal) t15 7).v ≤ 2451 / 10000) (hP7 : (SC.node Jm.toReal tj.toReal (eff t2.toReal) (eff t4.toReal) t15 7).p ≤ 1502 / 100000) :
    Near (E 1) (SC.tEnd Jm.toReal tj.toReal (eff t2.toReal) (eff t4.toReal) t15 1) (SC.node Jm.toReal tj.toReal (eff t2.toReal) (eff t4.toReal) t15 1) (299 / 1000000000) (127 / 500000000) (187 / 1000000000) (113 / 2500000000) ∧
    Near (E 2) (SC.tEnd Jm.toReal tj.toReal (eff t2.toReal) (eff t4.toReal) t15 2) (SC.node Jm.toReal tj.toReal (eff t2.toReal) (eff t4.toReal) t15 2) (299 / 500000000) (183 / 250000000) (11 / 15625000) (167 / 500000000) ∧
    Near (E 3) (SC.tEnd Jm.toReal tj.toReal (eff t2.toReal) (eff t4.toReal) t15 3) (SC.node Jm.toReal tj.toReal (eff t2.toReal) (eff t4.toReal) t15 3) (897 / 1000000000) (133 / 100000000) (127 / 100000000) (671 / 1000000000) ∧
    Near (E 4) (SC.tEnd Jm.toReal tj.toReal (eff t2.toReal) (eff t4.toReal) t15 4) (SC.node Jm.toReal tj.toReal (eff t2.toReal) (eff t4.toReal) t15 4) (3 / 2500000) (133 / 100000000) (3 / 500000) (1 / 78125) ∧
    Near (E 5) (SC.tEnd Jm.toReal tj.toReal (eff t2.toReal) (eff t4.toReal) t15 5) (SC.node Jm.toReal tj.toReal (eff t2.toReal) (eff t4.toReal) t15 5) (3 / 2000000) (159 / 100000000) (163 / 25000000) (9 / 625000) ∧
    Near (E 6) (SC.tEnd Jm.toReal tj.toReal (eff t2.toReal) (eff t4.toReal) t15 6) (SC.node Jm.toReal tj.toReal (eff t2.toReal) (eff t4.toReal) t15 6) (9 / 5000000) (207 / 100000000) (771 / 100000000) (181 / 10000000) ∧
    Near (E 7) (SC.tEnd Jm.toReal tj.toReal (eff t2.toReal) (eff t4.toReal) t15 7) (SC.node Jm.toReal tj.toReal (eff t2.toReal) (eff t4.toReal) t15 7) (21 / 10000000) (0) (431 / 50000000) (203 / 10000000) := by
  set N := SC.node Jm.toReal tj.toReal (eff t2.toReal) (eff t4.toReal) t15 with hN
  set tE := SC.tEnd Jm.toReal tj.toReal (eff t2.toReal) (eff t4.toReal) t15 with htE
  have hJ : |Jm.toReal| ≤ 6 := abs_le.2 ⟨by linarith [hP.J0], hP.J1⟩
  have fJn : (-Jm).IsFinite := (Float32.isFinite_neg _).2 fJ
  have hJn : |(-Jm).toReal| ≤ 6 := by rw [Float32.toReal_neg, abs_neg]; exact hJ
  have htj0 := hP.tj0
  have htj1 := hP.tj1
  have hpos : is_positive_float tj = true := sce_isPos ft (by linarith)
  have nb : ∀ k ≤ 22, |(N k).a| ≤ 2 ∧ 0 ≤ (N k).v ∧ (N k).v ≤ 3 := fun k hk => SC.node_bounds hP hk
  have pb : ∀ k ≤ 7, 0 ≤ (N k).p ∧ (N k).p ≤ 1502 / 100000 := fun k hk =>
    ⟨SC.pos_nonneg hP (by omega), (SC.pos_mono' hP hk (by norm_num)).trans hP7⟩
  have vb : ∀ k ≤ 7, 0 ≤ (N k).v ∧ (N k).v ≤ 2451 / 10000 := fun k hk =>
    ⟨(nb k (by omega)).2.1, (SC.vel_le7 hP hk).trans hV7⟩
  have tb : ∀ k ≤ 14, 0 ≤ tE k ∧ tE k ≤ 5 := fun k hk =>
    ⟨SC.tEnd_nonneg hP k, (SC.tEnd_le hP).1 k hk⟩
  have aL : (N 7).a = 0 := (SC.node_a (Jm := Jm.toReal) (tj := tj.toReal) (t2 := eff t2.toReal)
    (t4 := eff t4.toReal) (t15 := t15)).2.2.2.2.2.2.1
  have s0 : Near (E 0) (tE 0) (N 0) 0 0 0 0 := h0
  have s1 : Near (E 1) (tE 1) (N 1) (299 / 1000000000) (127 / 500000000) (187 / 1000000000) (113 / 2500000000) := by
    have ee : E 1 = incrE (E 0) tj Jm := by rw [hEs]; rfl
    have ne : N 1 = SC.incrNode (N 0) (Jm.toReal) (Real.pi / tj.toReal) tj.toReal := rfl
    have te : tE 1 = tE 0 + tj.toReal := rfl
    have tt := tb 1 (by norm_num)
    rw [te] at tt
    have h := near_incr (TM := 5) (AM := 2001 / 1000) (VM := 613 / 2500) (PM := 19 / 1250) s0 hpos ft
      (by linarith) htj1 (mag_t tt.1 tt.2 le_rfl) (by norm_num) (by norm_num) (mag_a (nb 0 (by norm_num)).1 (by norm_num)) (mag_v (vb 0 (by norm_num)).1 (vb 0 (by norm_num)).2 (by norm_num)) (mag_v (pb 0 (by norm_num)).1 (pb 0 (by norm_num)).2 (by norm_num))
      (fun a b c => fl_incr_S hL s0.fin.2.1 s0.fin.2.2.1 s0.fin.2.2.2 ft fJ htj0 htj1 hJ a b c)
    rw [ee, ne, te]
    exact h.mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s2 : Near (E 2) (tE 2) (N 2) (299 / 500000000) (183 / 250000000) (11 / 15625000) (167 / 500000000) := by
    have ee : E 2 = constE (E 1) t2 Jm := by rw [hEs]; rfl
    have ne : N 2 = SC.constNode (N 1) (Jm.toReal) (eff t2.toReal) := rfl
    have te : tE 2 = tE 1 + eff t2.toReal := rfl
    have tt := tb 2 (by norm_num)
    rw [ee, ne, te]
    rw [te] at tt
    rcases Bool.eq_false_or_eq_true (is_positive_float t2) with hp | hp
    · have he := eff_pos ft2 hp
      rw [he.1] at tt ⊢
      have h := near_const (D := 1 / 2) (TM := 5) (AM := 2001 / 1000) (VM := 613 / 2500) (PM := 19 / 1250) s1 hp ft2
        (by linarith) (by rw [← he.1]; exact hP.t21) (mag_t tt.1 tt.2 le_rfl) (by norm_num) (by norm_num) (mag_a (nb 1 (by norm_num)).1 (by norm_num)) (mag_v (vb 1 (by norm_num)).1 (vb 1 (by norm_num)).2 (by norm_num)) (mag_v (pb 1 (by norm_num)).1 (pb 1 (by norm_num)).2 (by norm_num))
        (fun a b c => fl_constJ_S hL s1.fin.2.1 s1.fin.2.2.1 s1.fin.2.2.2 ft2 fJ (by linarith) (by rw [← he.1]; exact hP.t21) hJ a b c)
      exact h.mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · have he := eff_neg ft2 hp
      rw [he.1]
      exact (near_gated s1 hp _).mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s3 : Near (E 3) (tE 3) (N 3) (897 / 1000000000) (133 / 100000000) (127 / 100000000) (671 / 1000000000) := by
    have ee : E 3 = decrE (E 2) tj Jm := by rw [hEs]; rfl
    have ne : N 3 = SC.decrNode (N 2) (Jm.toReal) (Real.pi / tj.toReal) tj.toReal := rfl
    have te : tE 3 = tE 2 + tj.toReal := rfl
    have tt := tb 3 (by norm_num)
    rw [te] at tt
    have h := near_decr (TM := 5) (AM := 2001 / 1000) (VM := 613 / 2500) (PM := 19 / 1250) s2 hpos ft
      (by linarith) htj1 (mag_t tt.1 tt.2 le_rfl) (by norm_num) (by norm_num) (mag_a (nb 2 (by norm_num)).1 (by norm_num)) (mag_v (vb 2 (by norm_num)).1 (vb 2 (by norm_num)).2 (by norm_num)) (mag_v (pb 2 (by norm_num)).1 (pb 2 (by norm_num)).2 (by norm_num))
      (fun a b c => fl_decr_S hL s2.fin.2.1 s2.fin.2.2.1 s2.fin.2.2.2 ft fJ htj0 htj1 hJ a b c)
    rw [ee, ne, te]
    exact h.mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s4 : Near (E 4) (tE 4) (N 4) (3 / 2500000) (133 / 100000000) (3 / 500000) (1 / 78125) := by
    have ee : E 4 = constE (E 3) t4 0.0 := by rw [hEs]; rfl
    have ne : N 4 = SC.constNode (N 3) (0) (eff t4.toReal) := rfl
    have te : tE 4 = tE 3 + eff t4.toReal := rfl
    have tt := tb 4 (by norm_num)
    rw [ee, ne, te]
    rw [te] at tt
    rcases Bool.eq_false_or_eq_true (is_positive_float t4) with hp | hp
    · have he := eff_pos ft4 hp
      rw [he.1] at tt ⊢
      have h := near_const0 (D := 3) (TM := 5) (AM := 2001 / 1000) (VM := 613 / 2500) (PM := 19 / 1250) s3 hp ft4
        (by linarith) (by rw [← he.1]; exact hP.t41) (mag_t tt.1 tt.2 le_rfl) (by norm_num) (by norm_num) (mag_a (nb 3 (by norm_num)).1 (by norm_num)) (mag_v (vb 3 (by norm_num)).1 (vb 3 (by norm_num)).2 (by norm_num)) (mag_v (pb 3 (by norm_num)).1 (pb 3 (by norm_num)).2 (by norm_num))
        (fun a b c => fl_const0_S hL s3.fin.2.1 s3.fin.2.2.1 s3.fin.2.2.2 ft4 (by linarith) (by rw [← he.1]; exact hP.t41) a b c)
      exact h.mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · have he := eff_neg ft4 hp
      rw [he.1]
      exact (near_gated s3 hp _).mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s5 : Near (E 5) (tE 5) (N 5) (3 / 2000000) (159 / 100000000) (163 / 25000000) (9 / 625000) := by
    have ee : E 5 = incrE (E 4) tj (-Jm) := by rw [hEs]; rfl
    have ne : N 5 = SC.incrNode (N 4) (-Jm.toReal) (Real.pi / tj.toReal) tj.toReal := rfl
    have te : tE 5 = tE 4 + tj.toReal := rfl
    have tt := tb 5 (by norm_num)
    rw [te] at tt
    have h := near_incr (TM := 5) (AM := 2001 / 1000) (VM := 613 / 2500) (PM := 19 / 1250) s4 hpos ft
      (by linarith) htj1 (mag_t tt.1 tt.2 le_rfl) (by norm_num) (by norm_num) (mag_a (nb 4 (by norm_num)).1 (by norm_num)) (mag_v (vb 4 (by norm_num)).1 (vb 4 (by norm_num)).2 (by norm_num)) (mag_v (pb 4 (by norm_num)).1 (pb 4 (by norm_num)).2 (by norm_num))
      (fun a b c => fl_incr_S hL s4.fin.2.1 s4.fin.2.2.1 s4.fin.2.2.2 ft fJn htj0 htj1 hJn a b c)
    rw [Float32.toReal_neg] at h
    rw [ee, ne, te]
    exact h.mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s6 : Near (E 6) (tE 6) (N 6) (9 / 5000000) (207 / 100000000) (771 / 100000000) (181 / 10000000) := by
    have ee : E 6 = constE (E 5) t2 (-Jm) := by rw [hEs]; rfl
    have ne : N 6 = SC.constNode (N 5) (-Jm.toReal) (eff t2.toReal) := rfl
    have te : tE 6 = tE 5 + eff t2.toReal := rfl
    have tt := tb 6 (by norm_num)
    rw [ee, ne, te]
    rw [te] at tt
    rcases Bool.eq_false_or_eq_true (is_positive_float t2) with hp | hp
    · have he := eff_pos ft2 hp
      rw [he.1] at tt ⊢
      have h := near_const (D := 1 / 2) (TM := 5) (AM := 2001 / 1000) (VM := 613 / 2500) (PM := 19 / 1250) s5 hp ft2
        (by linarith) (by rw [← he.1]; exact hP.t21) (mag_t tt.1 tt.2 le_rfl) (by norm_num) (by norm_num) (mag_a (nb 5 (by norm_num)).1 (by norm_num)) (mag_v (vb 5 (by norm_num)).1 (vb 5 (by norm_num)).2 (by norm_num)) (mag_v (pb 5 (by norm_num)).1 (pb 5 (by norm_num)).2 (by norm_num))
        (fun a b c => fl_constJ_S hL s5.fin.2.1 s5.fin.2.2.1 s5.fin.2.2.2 ft2 fJn (by linarith) (by rw [← he.1]; exact hP.t21) hJn a b c)
      rw [Float32.toReal_neg] at h
      exact h.mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · have he := eff_neg ft2 hp
      rw [he.1]
      exact (near_gated s5 hp _).mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s7 : Near (E 7) (tE 7) (N 7) (21 / 10000000) (0) (431 / 50000000) (203 / 10000000) := by
    have ee : E 7 = { decrE (E 6) tj (-Jm) with end_accel := 0.0 } := by rw [hEs]; rfl
    have ne : N 7 = SC.decrNode (N 6) (-Jm.toReal) (Real.pi / tj.toReal) tj.toReal := rfl
    have te : tE 7 = tE 6 + tj.toReal := rfl
    have tt := tb 7 (by norm_num)
    rw [te] at tt
    have h := near_decr (TM := 5) (AM := 2001 / 1000) (VM := 613 / 2500) (PM := 19 / 1250) s6 hpos ft
      (by linarith) htj1 (mag_t tt.1 tt.2 le_rfl) (by norm_num) (by norm_num) (mag_a (nb 6 (by norm_num)).1 (by norm_num)) (mag_v (vb 6 (by norm_num)).1 (vb 6 (by norm_num)).2 (by norm_num)) (mag_v (pb 6 (by norm_num)).1 (pb 6 (by norm_num)).2 (by norm_num))
      (fun a b c => fl_decr_S hL s6.fin.2.1 s6.fin.2.2.1 s6.fin.2.2.2 ft fJn htj0 htj1 hJn a b c)
    rw [Float32.toReal_neg] at h
    rw [ee, ne, te]
    rw [← ne] at h ⊢
    exact (h.zeroA aL).mono (by norm_num) le_rfl (by norm_num) (by norm_num)
  exact ⟨s1, s2, s3, s4, s5, s6, s7⟩

set_option maxHeartbeats 8000000 in
/-- **The decelerating phase**, regime `G`. -/
theorem decel_G (hL : LibmSpec) {L Jm tj t2 t4 : Float32} {E : ℕ → SCurve.segment_t}
    (hEs : ∀ k, E (k + 1) = stepE L Jm tj t2 t4 t2 k (E k))
    (fJ : Jm.IsFinite) (ft : tj.IsFinite) (ft2 : t2.IsFinite) (ft4 : t4.IsFinite)
    {t15 : ℝ} (hP : SC.ProfIn Jm.toReal tj.toReal (eff t2.toReal) (eff t4.toReal) t15)
    (h15 : t15 ≤ 15) (hP22 : (SC.node Jm.toReal tj.toReal (eff t2.toReal) (eff t4.toReal) t15 22).p ≤ 37 / 10)
    (s15 : Near (E 15) (SC.tEnd Jm.toReal tj.toReal (eff t2.toReal) (eff t4.toReal) t15 15) (SC.node Jm.toReal tj.toReal (eff t2.toReal) (eff t4.toReal) t15 15) (33 / 10000000) (0) (113 / 10000000) (209 / 1000000)) :
    Near (E 16) (SC.tEnd Jm.toReal tj.toReal (eff t2.toReal) (eff t4.toReal) t15 16) (SC.node Jm.toReal tj.toReal (eff t2.toReal) (eff t4.toReal) t15 16) (3 / 625000) (127 / 500000000) (119 / 10000000) (213 / 1000000) ∧
    Near (E 17) (SC.tEnd Jm.toReal tj.toReal (eff t2.toReal) (eff t4.toReal) t15 17) (SC.node Jm.toReal tj.toReal (eff t2.toReal) (eff t4.toReal) t15 17) (63 / 10000000) (183 / 250000000) (1 / 78125) (221 / 1000000) ∧
    Near (E 18) (SC.tEnd Jm.toReal tj.toReal (eff t2.toReal) (eff t4.toReal) t15 18) (SC.node Jm.toReal tj.toReal (eff t2.toReal) (eff t4.toReal) t15 18) (39 / 5000000) (133 / 100000000) (139 / 10000000) (113 / 500000) ∧
    Near (E 19) (SC.tEnd Jm.toReal tj.toReal (eff t2.toReal) (eff t4.toReal) t15 19) (SC.node Jm.toReal tj.toReal (eff t2.toReal) (eff t4.toReal) t15 19) (93 / 10000000) (133 / 100000000) (47 / 2500000) (139 / 500000) ∧
    Near (E 20) (SC.tEnd Jm.toReal tj.toReal (eff t2.toReal) (eff t4.toReal) t15 20) (SC.node Jm.toReal tj.toReal (eff t2.toReal) (eff t4.toReal) t15 20) (27 / 2500000) (159 / 100000000) (197 / 10000000) (71 / 250000) ∧
    Near (E 21) (SC.tEnd Jm.toReal tj.toReal (eff t2.toReal) (eff t4.toReal) t15 21) (SC.node Jm.toReal tj.toReal (eff t2.toReal) (eff t4.toReal) t15 21) (123 / 10000000) (207 / 100000000) (213 / 10000000) (37 / 125000) ∧
    Near (E 22) (SC.tEnd Jm.toReal tj.toReal (eff t2.toReal) (eff t4.toReal) t15 22) (SC.node Jm.toReal tj.toReal (eff t2.toReal) (eff t4.toReal) t15 22) (69 / 5000000) (0) (0) (303 / 1000000) := by
  set N := SC.node Jm.toReal tj.toReal (eff t2.toReal) (eff t4.toReal) t15 with hN
  set tE := SC.tEnd Jm.toReal tj.toReal (eff t2.toReal) (eff t4.toReal) t15 with htE
  have hJ : |Jm.toReal| ≤ 6 := abs_le.2 ⟨by linarith [hP.J0], hP.J1⟩
  have fJn : (-Jm).IsFinite := (Float32.isFinite_neg _).2 fJ
  have hJn : |(-Jm).toReal| ≤ 6 := by rw [Float32.toReal_neg, abs_neg]; exact hJ
  have htj0 := hP.tj0
  have htj1 := hP.tj1
  have hpos : is_positive_float tj = true := sce_isPos ft (by linarith)
  have nb : ∀ k ≤ 22, |(N k).a| ≤ 2 ∧ 0 ≤ (N k).v ∧ (N k).v ≤ 3 := fun k hk => SC.node_bounds hP hk
  have pb : ∀ k ≤ 22, 0 ≤ (N k).p ∧ (N k).p ≤ 37 / 10 := fun k hk =>
    ⟨SC.pos_nonneg hP hk, (SC.pos_mono' hP hk le_rfl).trans hP22⟩
  have vb : ∀ k ≤ 22, 0 ≤ (N k).v ∧ (N k).v ≤ 3 := fun k hk => ⟨(nb k hk).2.1, (nb k hk).2.2⟩
  have tb : ∀ k ≤ 22, 0 ≤ tE k ∧ tE k ≤ 25 := fun k hk =>
    ⟨SC.tEnd_nonneg hP k, by linarith [(SC.tEnd_le hP).2 k hk]⟩
  have n22 := SC.node_22_eq (Jm := Jm.toReal) (tj := tj.toReal) (t2 := eff t2.toReal)
    (t4 := eff t4.toReal) (t15 := t15) (by linarith [hP.tj0])
  have aL : (N 22).a = 0 := by rw [hN, n22]
  have vL : (N 22).v = 0 := by rw [hN, n22]
  have s16 : Near (E 16) (tE 16) (N 16) (3 / 625000) (127 / 500000000) (119 / 10000000) (213 / 1000000) := by
    have ee : E 16 = incrE (E 15) tj (-Jm) := by rw [hEs]; rfl
    have ne : N 16 = SC.incrNode (N 15) (-Jm.toReal) (Real.pi / tj.toReal) tj.toReal := rfl
    have te : tE 16 = tE 15 + tj.toReal := rfl
    have tt := tb 16 (by norm_num)
    rw [te] at tt
    have h := near_incr (TM := 25) (AM := 2001 / 1000) (VM := 3001 / 1000) (PM := 4001 / 1000) s15 hpos ft
      (by linarith) htj1 (mag_t tt.1 tt.2 le_rfl) (by norm_num) (by norm_num) (mag_a (nb 15 (by norm_num)).1 (by norm_num)) (mag_v (vb 15 (by norm_num)).1 (vb 15 (by norm_num)).2 (by norm_num)) (mag_v (pb 15 (by norm_num)).1 (pb 15 (by norm_num)).2 (by norm_num))
      (fun a b c => fl_incr_G hL s15.fin.2.1 s15.fin.2.2.1 s15.fin.2.2.2 ft fJn htj0 htj1 hJn a b c)
    rw [Float32.toReal_neg] at h
    rw [ee, ne, te]
    exact h.mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s17 : Near (E 17) (tE 17) (N 17) (63 / 10000000) (183 / 250000000) (1 / 78125) (221 / 1000000) := by
    have ee : E 17 = constE (E 16) t2 (-Jm) := by rw [hEs]; rfl
    have ne : N 17 = SC.constNode (N 16) (-Jm.toReal) (eff t2.toReal) := rfl
    have te : tE 17 = tE 16 + eff t2.toReal := rfl
    have tt := tb 17 (by norm_num)
    rw [ee, ne, te]
    rw [te] at tt
    rcases Bool.eq_false_or_eq_true (is_positive_float t2) with hp | hp
    · have he := eff_pos ft2 hp
      rw [he.1] at tt ⊢
      have h := near_const (D := 1 / 2) (TM := 25) (AM := 2001 / 1000) (VM := 3001 / 1000) (PM := 4001 / 1000) s16 hp ft2
        (by linarith) (by rw [← he.1]; exact hP.t21) (mag_t tt.1 tt.2 le_rfl) (by norm_num) (by norm_num) (mag_a (nb 16 (by norm_num)).1 (by norm_num)) (mag_v (vb 16 (by norm_num)).1 (vb 16 (by norm_num)).2 (by norm_num)) (mag_v (pb 16 (by norm_num)).1 (pb 16 (by norm_num)).2 (by norm_num))
        (fun a b c => fl_constJ_G hL s16.fin.2.1 s16.fin.2.2.1 s16.fin.2.2.2 ft2 fJn (by linarith) (by rw [← he.1]; exact hP.t21) hJn a b c)
      rw [Float32.toReal_neg] at h
      exact h.mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · have he := eff_neg ft2 hp
      rw [he.1]
      exact (near_gated s16 hp _).mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s18 : Near (E 18) (tE 18) (N 18) (39 / 5000000) (133 / 100000000) (139 / 10000000) (113 / 500000) := by
    have ee : E 18 = decrE (E 17) tj (-Jm) := by rw [hEs]; rfl
    have ne : N 18 = SC.decrNode (N 17) (-Jm.toReal) (Real.pi / tj.toReal) tj.toReal := rfl
    have te : tE 18 = tE 17 + tj.toReal := rfl
    have tt := tb 18 (by norm_num)
    rw [te] at tt
    have h := near_decr (TM := 25) (AM := 2001 / 1000) (VM := 3001 / 1000) (PM := 4001 / 1000) s17 hpos ft
      (by linarith) htj1 (mag_t tt.1 tt.2 le_rfl) (by norm_num) (by norm_num) (mag_a (nb 17 (by norm_num)).1 (by norm_num)) (mag_v (vb 17 (by norm_num)).1 (vb 17 (by norm_num)).2 (by norm_num)) (mag_v (pb 17 (by norm_num)).1 (pb 17 (by norm_num)).2 (by norm_num))
      (fun a b c => fl_decr_G hL s17.fin.2.1 s17.fin.2.2.1 s17.fin.2.2.2 ft fJn htj0 htj1 hJn a b c)
    rw [Float32.toReal_neg] at h
    rw [ee, ne, te]
    exact h.mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s19 : Near (E 19) (tE 19) (N 19) (93 / 10000000) (133 / 100000000) (47 / 2500000) (139 / 500000) := by
    have ee : E 19 = constE (E 18) t4 0.0 := by rw [hEs]; rfl
    have ne : N 19 = SC.constNode (N 18) (0) (eff t4.toReal) := rfl
    have te : tE 19 = tE 18 + eff t4.toReal := rfl
    have tt := tb 19 (by norm_num)
    rw [ee, ne, te]
    rw [te] at tt
    rcases Bool.eq_false_or_eq_true (is_positive_float t4) with hp | hp
    · have he := eff_pos ft4 hp
      rw [he.1] at tt ⊢
      have h := near_const0 (D := 3) (TM := 25) (AM := 2001 / 1000) (VM := 3001 / 1000) (PM := 4001 / 1000) s18 hp ft4
        (by linarith) (by rw [← he.1]; exact hP.t41) (mag_t tt.1 tt.2 le_rfl) (by norm_num) (by norm_num) (mag_a (nb 18 (by norm_num)).1 (by norm_num)) (mag_v (vb 18 (by norm_num)).1 (vb 18 (by norm_num)).2 (by norm_num)) (mag_v (pb 18 (by norm_num)).1 (pb 18 (by norm_num)).2 (by norm_num))
        (fun a b c => fl_const0_G hL s18.fin.2.1 s18.fin.2.2.1 s18.fin.2.2.2 ft4 (by linarith) (by rw [← he.1]; exact hP.t41) a b c)
      exact h.mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · have he := eff_neg ft4 hp
      rw [he.1]
      exact (near_gated s18 hp _).mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s20 : Near (E 20) (tE 20) (N 20) (27 / 2500000) (159 / 100000000) (197 / 10000000) (71 / 250000) := by
    have ee : E 20 = incrE (E 19) tj Jm := by rw [hEs]; rfl
    have ne : N 20 = SC.incrNode (N 19) (Jm.toReal) (Real.pi / tj.toReal) tj.toReal := rfl
    have te : tE 20 = tE 19 + tj.toReal := rfl
    have tt := tb 20 (by norm_num)
    rw [te] at tt
    have h := near_incr (TM := 25) (AM := 2001 / 1000) (VM := 3001 / 1000) (PM := 4001 / 1000) s19 hpos ft
      (by linarith) htj1 (mag_t tt.1 tt.2 le_rfl) (by norm_num) (by norm_num) (mag_a (nb 19 (by norm_num)).1 (by norm_num)) (mag_v (vb 19 (by norm_num)).1 (vb 19 (by norm_num)).2 (by norm_num)) (mag_v (pb 19 (by norm_num)).1 (pb 19 (by norm_num)).2 (by norm_num))
      (fun a b c => fl_incr_G hL s19.fin.2.1 s19.fin.2.2.1 s19.fin.2.2.2 ft fJ htj0 htj1 hJ a b c)
    rw [ee, ne, te]
    exact h.mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s21 : Near (E 21) (tE 21) (N 21) (123 / 10000000) (207 / 100000000) (213 / 10000000) (37 / 125000) := by
    have ee : E 21 = constE (E 20) t2 Jm := by rw [hEs]; rfl
    have ne : N 21 = SC.constNode (N 20) (Jm.toReal) (eff t2.toReal) := rfl
    have te : tE 21 = tE 20 + eff t2.toReal := rfl
    have tt := tb 21 (by norm_num)
    rw [ee, ne, te]
    rw [te] at tt
    rcases Bool.eq_false_or_eq_true (is_positive_float t2) with hp | hp
    · have he := eff_pos ft2 hp
      rw [he.1] at tt ⊢
      have h := near_const (D := 1 / 2) (TM := 25) (AM := 2001 / 1000) (VM := 3001 / 1000) (PM := 4001 / 1000) s20 hp ft2
        (by linarith) (by rw [← he.1]; exact hP.t21) (mag_t tt.1 tt.2 le_rfl) (by norm_num) (by norm_num) (mag_a (nb 20 (by norm_num)).1 (by norm_num)) (mag_v (vb 20 (by norm_num)).1 (vb 20 (by norm_num)).2 (by norm_num)) (mag_v (pb 20 (by norm_num)).1 (pb 20 (by norm_num)).2 (by norm_num))
        (fun a b c => fl_constJ_G hL s20.fin.2.1 s20.fin.2.2.1 s20.fin.2.2.2 ft2 fJ (by linarith) (by rw [← he.1]; exact hP.t21) hJ a b c)
      exact h.mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · have he := eff_neg ft2 hp
      rw [he.1]
      exact (near_gated s20 hp _).mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have s22 : Near (E 22) (tE 22) (N 22) (69 / 5000000) (0) (0) (303 / 1000000) := by
    have ee : E 22 = { decrE (E 21) tj Jm with end_accel := 0.0, end_vel := 0.0 } := by rw [hEs]; rfl
    have ne : N 22 = SC.decrNode (N 21) (Jm.toReal) (Real.pi / tj.toReal) tj.toReal := rfl
    have te : tE 22 = tE 21 + tj.toReal := rfl
    have tt := tb 22 (by norm_num)
    rw [te] at tt
    have h := near_decr (TM := 25) (AM := 2001 / 1000) (VM := 3001 / 1000) (PM := 4001 / 1000) s21 hpos ft
      (by linarith) htj1 (mag_t tt.1 tt.2 le_rfl) (by norm_num) (by norm_num) (mag_a (nb 21 (by norm_num)).1 (by norm_num)) (mag_v (vb 21 (by norm_num)).1 (vb 21 (by norm_num)).2 (by norm_num)) (mag_v (pb 21 (by norm_num)).1 (pb 21 (by norm_num)).2 (by norm_num))
      (fun a b c => fl_decr_G hL s21.fin.2.1 s21.fin.2.2.1 s21.fin.2.2.2 ft fJ htj0 htj1 hJ a b c)
    rw [ee, ne, te]
    rw [← ne] at h ⊢
    exact (h.zeroAV aL vL).mono (by norm_num) le_rfl le_rfl (by norm_num)
  exact ⟨s16, s17, s18, s19, s20, s21, s22⟩

end SCT

end

end Contracts.Mission
