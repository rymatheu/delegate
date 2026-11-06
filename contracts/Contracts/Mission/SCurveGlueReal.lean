import Contracts.Mission.SCurveProfile

/-!
# Glue for `SCurve::get_jerk_accel_vel_pos_at_time`: real estimates

The error chain from a segment's closed form at the code's local time to the profile `SC.profPos`
(`chain`), and the sensitivity of the closed forms to the `float` start node and duration
(`const_core`, `ramp_core`).
-/

namespace Contracts.Mission

namespace SCG

open SC

variable {Jm tj t2 t4 t15 : ℝ}

/-- Durations, kinds and jerks of the profile's segments. -/
theorem prof_facts (h : ProfIn Jm tj t2 t4 t15) (h15 : t15 ≤ 15) {j : ℕ} (hj : j < 22) :
    (prof Jm tj t2 t4 t15 j).d ≤ 15 ∧
    ((prof Jm tj t2 t4 t15 j).kind ≠ .const → (prof Jm tj t2 t4 t15 j).d = tj) ∧
    (j ≠ 14 → (prof Jm tj t2 t4 t15 j).d ≤ 3) ∧
    ((prof Jm tj t2 t4 t15 j).kind = .const →
      (prof Jm tj t2 t4 t15 j).J = 0 ∨ (prof Jm tj t2 t4 t15 j).d ≤ 1 / 2) ∧
    (j = 14 → (prof Jm tj t2 t4 t15 j).J = 0) := by
  have := h.tj1; have := h.t21; have := h.t41; have := h.tj0
  refine ⟨?_, fun hk => ?_, fun hk => ?_, fun hk => ?_, fun hk => ?_⟩
  · interval_cases j <;> simp only [prof] <;> linarith
  · interval_cases j <;> simp only [prof] at hk ⊢ <;> exact absurd rfl hk
  · interval_cases j <;> simp only [prof] <;> first | linarith | exact absurd rfl hk
  · interval_cases j <;> simp only [prof] at hk ⊢ <;>
      first | (left; rfl) | (left; trivial) | (right; linarith)
  · subst hk; rfl

/-- Nodes of segments of positive duration lie between `0` and the end node. -/
theorem node_p (h : ProfIn Jm tj t2 t4 t15) {j : ℕ} (hj : j < 22)
    (hd : 0 < (prof Jm tj t2 t4 t15 j).d) :
    0 ≤ (node Jm tj t2 t4 t15 j).p ∧ (node Jm tj t2 t4 t15 j).p ≤ (node Jm tj t2 t4 t15 22).p := by
  have e := profPos_seg h hj (τ := 0) ⟨le_rfl, hd.le⟩
  rw [add_zero, (Seg.at_zero _ _ hd).2.2] at e
  rw [← e, ← profPos_of_ge h le_rfl, ← profPos_of_le h (le_refl 0)]
  exact ⟨profPos_mono h (tEnd_nonneg h j), profPos_mono h (tEnd_mono h (by omega))⟩

/-- **The chain**: a value within `E` of segment `j`'s closed form at the code's local time `τ`
(a rounding of `t − T_j`, with `T_j ≤ t < T_{j+1}` the table's end times) is within `E + 1/4000`
of the profile at `t`. -/
theorem chain (h : ProfIn Jm tj t2 t4 t15) (h15 : t15 ≤ 15) {j : ℕ} (hj : j < 22)
    {t Tj Tk τ Q E : ℝ} (hTj : |Tj - tEnd Jm tj t2 t4 t15 j| ≤ 2 / 10 ^ 5)
    (hTk : |Tk - tEnd Jm tj t2 t4 t15 (j + 1)| ≤ 2 / 10 ^ 5) (hle : Tj ≤ t) (hlt : t < Tk)
    (hτ : |τ - (t - Tj)| ≤ 1 / 16777216 * (t - Tj))
    (hQ : |Q - (prof Jm tj t2 t4 t15 j).pos (node Jm tj t2 t4 t15 j) τ| ≤ E) :
    |Q - profPos Jm tj t2 t4 t15 t| ≤ E + 1 / 4000 := by
  obtain ⟨hd0, -, hte⟩ := prof_d h hj
  have hd15 := (prof_facts h h15 hj).1
  set d := (prof Jm tj t2 t4 t15 j).d with hd
  set T := tEnd Jm tj t2 t4 t15 j with hT
  rw [hte] at hTk
  obtain ⟨a1, a2⟩ := abs_le.1 hTj
  obtain ⟨b1, b2⟩ := abs_le.1 hTk
  obtain ⟨c1, c2⟩ := abs_le.1 hτ
  have h1 : t - Tj ≤ d + 4 / 10 ^ 5 := by linarith
  have h2 : 1 / 16777216 * (t - Tj) ≤ 1 / 1000000 := by nlinarith
  have hτ0 : 0 ≤ τ := by nlinarith
  have l1 := seg_lip h hj (τ := τ) (τ' := t - T) ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩
  have l2 := seg_ext h hj (τ := t - T) ⟨by linarith, by linarith⟩
  rw [show T + (t - T) = t by ring] at l2
  have hm : max (-(t - T)) 0 + max (t - T - d) 0 ≤ 2 / 10 ^ 5 := by
    rcases le_total (t - T) 0 with h3 | h3
    · rw [max_eq_left (by linarith), max_eq_right (by linarith)]; linarith
    · rw [max_eq_right (by linarith)]
      rcases le_total (t - T - d) 0 with h4 | h4
      · rw [max_eq_right h4]; norm_num
      · rw [max_eq_left h4]; linarith
  have hττ : |τ - (t - T)| ≤ 21 / 10 ^ 6 := abs_le.2 ⟨by linarith, by linarith⟩
  have q1 := abs_le.1 hQ
  have q2 := abs_le.1 l1
  have q3 := abs_le.1 l2
  exact abs_le.2 ⟨by linarith, by linarith⟩

theorem seg_eta {s : Seg} {k : Kind} (h : s.kind = k) : s = ⟨k, s.J, s.d⟩ := by
  cases s; cases h; rfl

/-- **Constant jerk**: the `float` closed form (error of `eval_const`) at the `float` node against
the real closed form at the real node. -/
theorem const_core {J d τ Q : ℝ} {n n' : Node} (hτ : 0 ≤ τ) (hJ6 : |J| ≤ 6)
    (hQ : |Q - cP n' J τ| ≤ 16 / 16777216 * (|n'.p| + |n'.v| * τ + |n'.a| * τ ^ 2 + |J| * τ ^ 3) +
      1 / 2 ^ 100)
    (hp : |n'.p| ≤ 5) (hv : |n'.v| * τ ≤ 46) (ha : |n'.a| * τ ^ 2 ≤ 19) (hj : |J| * τ ^ 3 ≤ 1)
    (ep : |n'.p - n.p| ≤ 4 / 10 ^ 4) (ev : |n'.v - n.v| * τ ≤ 46 / 10 ^ 5)
    (ea : |n'.a - n.a| * τ ^ 2 ≤ 1 / 10 ^ 4) :
    |Q - Seg.pos ⟨.const, J, d⟩ n τ| ≤ 1 / 1000 := by
  have s := seg_sens .const (J := J) (d := d) (d' := d) (τ := τ) n n' hJ6 (fun h => absurd rfl h) hτ
  rw [sub_self, abs_zero, mul_zero, add_zero] at s
  have e : Seg.pos ⟨.const, J, d⟩ n' τ = cP n' J τ := rfl
  rw [e] at s
  have q1 := abs_le.1 hQ
  have q2 := abs_le.1 s
  have := abs_nonneg n'.p
  refine abs_le.2 ⟨?_, ?_⟩ <;> nlinarith

/-- **Ramps**: the `float` closed form (within `10⁻⁴`) at the `float` node and duration against the
real closed form at the real node and duration. -/
theorem ramp_core {k : Kind} (_hk : k ≠ .const) {J d d' τ Q : ℝ} {n n' : Node} (hτ : 0 ≤ τ)
    (hτ2 : τ ≤ 2 * d) (hd1 : 1 / 300 ≤ d) (hd2 : d ≤ 1 / 4) (hdd : |d' - d| ≤ 1 / 10 ^ 5)
    (hJ6 : |J| ≤ 6) (hQ : |Q - Seg.pos ⟨k, J, d'⟩ n' τ| ≤ 1 / 10 ^ 4)
    (ep : |n'.p - n.p| ≤ 4 / 10 ^ 4) (ev : |n'.v - n.v| ≤ 3 / 10 ^ 5)
    (ea : |n'.a - n.a| ≤ 1 / 10 ^ 5) :
    |Q - Seg.pos ⟨k, J, d⟩ n τ| ≤ 1 / 1000 := by
  have s := seg_sens k (J := J) (d := d) (d' := d') (τ := τ) n n' hJ6
    (fun _ => ⟨hd1, hd2, hdd.trans (by norm_num), hτ2⟩) hτ
  have hτ' : τ ≤ 1 / 2 := by linarith
  have v1 : |n'.v - n.v| * τ ≤ 3 / 10 ^ 5 * (1 / 2) :=
    mul_le_mul ev hτ' hτ (by norm_num)
  have v2 : |n'.a - n.a| * τ ^ 2 ≤ 1 / 10 ^ 5 * (1 / 2) ^ 2 :=
    mul_le_mul ea (pow_le_pow_left₀ hτ hτ' 2) (by positivity) (by norm_num)
  have q1 := abs_le.1 hQ
  have q2 := abs_le.1 s
  refine abs_le.2 ⟨?_, ?_⟩ <;> linarith

/-- The final `MAX(0, ·)` only brings the value closer to a nonnegative target. -/
theorem max_close {x y : ℝ} (hy : 0 ≤ y) : |max 0 x - y| ≤ |x - y| := by
  rcases le_total x 0 with h | h
  · rw [max_eq_left h, zero_sub, abs_neg, abs_of_nonneg hy, abs_sub_comm,
      abs_of_nonneg (by linarith)]; linarith
  · rw [max_eq_right h]

end SCG

end Contracts.Mission
