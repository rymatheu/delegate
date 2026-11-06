import Contracts.Mission.SCurveProfile
import Contracts.Mission.SCurveCalc

/-!
# Facts about the real profile used by the table bounds

Positions are nondecreasing along the nodes and nonnegative, velocities increase through the
accelerating phase, the start times are bounded by the durations, and the node `7` (end of the
accelerating phase) is bounded by the half leg.
-/

namespace Contracts.Mission.SC

open Real Set

noncomputable section

variable {Jm tj t2 t4 t15 : ℝ}

theorem pos_step (h : ProfIn Jm tj t2 t4 t15) {k : ℕ} (hk : k < 22) :
    (node Jm tj t2 t4 t15 k).p ≤ (node Jm tj t2 t4 t15 (k + 1)).p := by
  have htj : 0 < tj := by linarith [h.tj0]
  have ok := prof_ok (Jm := Jm) htj h.t20 h.t40 h.t150 k
  obtain ⟨-, hm⟩ := (prof_mono h.J0.le htj h.t20 h.t40 h.t150).2 k hk
  obtain ⟨⟨-, -, e0⟩, ⟨-, -, ed⟩⟩ := Seg.ends ok (node Jm tj t2 t4 t15 k)
  have hd := ok.d_nonneg
  have := hm ⟨le_rfl, hd⟩ ⟨hd, le_rfl⟩ hd
  rw [e0, ed] at this
  exact this

theorem pos_mono' (h : ProfIn Jm tj t2 t4 t15) {i j : ℕ} (hij : i ≤ j) (hj : j ≤ 22) :
    (node Jm tj t2 t4 t15 i).p ≤ (node Jm tj t2 t4 t15 j).p := by
  induction j, hij using Nat.le_induction with
  | base => exact le_rfl
  | succ j hij ih => exact (ih (by omega)).trans (pos_step h (by omega))

theorem pos_nonneg (h : ProfIn Jm tj t2 t4 t15) {k : ℕ} (hk : k ≤ 22) :
    0 ≤ (node Jm tj t2 t4 t15 k).p :=
  pos_mono' h (Nat.zero_le k) hk

theorem vel_up (h : ProfIn Jm tj t2 t4 t15) {k : ℕ} (hk : k < 7) :
    (node Jm tj t2 t4 t15 k).v ≤ (node Jm tj t2 t4 t15 (k + 1)).v := by
  have htj : 0 < tj := by linarith [h.tj0]
  have hJm : 0 ≤ Jm := h.J0.le
  have h2 := h.t20
  have ok := prof_ok (Jm := Jm) htj h.t20 h.t40 h.t150
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, -⟩ :=
    node_a (Jm := Jm) (tj := tj) (t2 := t2) (t4 := t4) (t15 := t15)
  set N := node Jm tj t2 t4 t15 with hN
  set S := prof Jm tj t2 t4 t15 with hS
  have hNs : ∀ k, N (k + 1) = (S k).node (N k) := fun k => rfl
  have a0 : (N 0).a = 0 := rfl
  have hJt : 0 ≤ Jm * tj / 2 := by positivity
  have hJt2 : 0 ≤ Jm * t2 := by positivity
  have hJs : ∀ k, 0 ≤ (S k).J ∨ (S k).J ≤ 0 := fun k => le_total 0 _
  have hA0 : 0 ≤ (N k).a := by
    interval_cases k <;> simp only [a0, a1, a2, a3, a4, a5, a6] <;> positivity
  have hAd : 0 ≤ (N (k + 1)).a := by
    interval_cases k <;> simp only [a1, a2, a3, a4, a5, a6, a7, zero_add] <;> positivity
  rw [hNs] at hAd ⊢
  exact (Seg.acc_nonneg (ok k) _ (hJs k) hA0 hAd).2

theorem vel_le7 (h : ProfIn Jm tj t2 t4 t15) {k : ℕ} (hk : k ≤ 7) :
    (node Jm tj t2 t4 t15 k).v ≤ (node Jm tj t2 t4 t15 7).v := by
  have u0 := vel_up h (k := 0) (by norm_num)
  have u1 := vel_up h (k := 1) (by norm_num)
  have u2 := vel_up h (k := 2) (by norm_num)
  have u3 := vel_up h (k := 3) (by norm_num)
  have u4 := vel_up h (k := 4) (by norm_num)
  have u5 := vel_up h (k := 5) (by norm_num)
  have u6 := vel_up h (k := 6) (by norm_num)
  interval_cases k <;> linarith

theorem tEnd_le (h : ProfIn Jm tj t2 t4 t15) :
    (∀ k ≤ 14, tEnd Jm tj t2 t4 t15 k ≤ 5) ∧ (∀ k ≤ 22, tEnd Jm tj t2 t4 t15 k ≤ 10 + t15) := by
  have h1 := h.tj1; have h2 := h.t21; have h4 := h.t41; have h0 := h.tj0
  have h20 := h.t20; have h40 := h.t40; have h15 := h.t150
  have e : ∀ k, tEnd Jm tj t2 t4 t15 (k + 1) = tEnd Jm tj t2 t4 t15 k + (prof Jm tj t2 t4 t15 k).d :=
    fun k => rfl
  have t0 : tEnd Jm tj t2 t4 t15 0 = 0 := rfl
  have b7 : ∀ k ≤ 14, tEnd Jm tj t2 t4 t15 k ≤ 5 := by
    intro k hk
    interval_cases k <;> simp only [e, t0, prof] <;> linarith
  refine ⟨b7, fun k hk => ?_⟩
  by_cases hk' : k ≤ 14
  · linarith [b7 k hk']
  have b14 := b7 14 le_rfl
  interval_cases k <;> simp only [e, prof] <;> linarith

end

end Contracts.Mission.SC
