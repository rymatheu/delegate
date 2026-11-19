import Contracts.Mission.SCurveReal

/-!
# The S-curve profile as a function of time (over the reals)

The 22 segments of `add_segments` (`prof`, `node` of `SCurveReal.lean`) laid end to end: `tEnd k`
is the start time of segment `k` (code segment `k + 1`), and `profPos t` the position at time `t`,
written as the sum of the clamped increments of the segments (no search for the current segment).
Properties: monotone, between `0` and the end node, equal to the segment's closed form on the
segment, Lipschitz; the closed form of a segment extended a little beyond its ends stays close to
`profPos`; and the closed forms depend Lipschitz-continuously on the start node and the duration.
-/

namespace Contracts.Mission.SC

open Real

noncomputable section

/-- The start time of segment `k`. -/
def tEnd (Jm tj t2 t4 t15 : ℝ) : ℕ → ℝ
  | 0 => 0
  | k + 1 => tEnd Jm tj t2 t4 t15 k + (prof Jm tj t2 t4 t15 k).d

/-- Segment `k`'s closed form at time `t`, with the segment's local time clamped to `[0, d]`. -/
def segAt (Jm tj t2 t4 t15 : ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  (prof Jm tj t2 t4 t15 k).pos (node Jm tj t2 t4 t15 k)
    (max 0 (min (t - tEnd Jm tj t2 t4 t15 k) (prof Jm tj t2 t4 t15 k).d))

/-- **The profile's position at time `t`**: the sum of the segments' clamped increments. -/
def profPos (Jm tj t2 t4 t15 : ℝ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.range 22, (segAt Jm tj t2 t4 t15 k t - (node Jm tj t2 t4 t15 k).p)

/-- The ranges of the profile's parameters on the mission (from `calculate_path`). -/
structure ProfIn (Jm tj t2 t4 t15 : ℝ) : Prop where
  J0 : 0 < Jm
  J1 : Jm ≤ 6
  tj0 : 1 / 300 ≤ tj
  tj1 : tj ≤ 1 / 4
  t20 : 0 ≤ t2
  t21 : t2 ≤ 1 / 2
  t40 : 0 ≤ t4
  t41 : t4 ≤ 3
  t150 : 0 ≤ t15
  A : Jm * (tj + t2) ≤ 2
  V : Jm * (tj + t2) * (2 * tj + t2 + t4) ≤ 3

variable {Jm tj t2 t4 t15 : ℝ}

open Set

/-! ## Generic estimates -/

/-- A derivative bound on an interval gives a Lipschitz bound there. -/
theorem lip_of_deriv {f f' : ℝ → ℝ} {a b M : ℝ} (hf : ∀ t, HasDerivAt f (f' t) t)
    (hM : ∀ t ∈ Icc a b, |f' t| ≤ M) {x y : ℝ} (hx : x ∈ Icc a b) (hy : y ∈ Icc a b) :
    |f x - f y| ≤ M * |x - y| := by
  have := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := f) (f' := f')
    (fun t _ => (hf t).hasDerivWithinAt) (fun t ht => by rw [Real.norm_eq_abs]; exact hM t ht)
    (convex_Icc a b) hy hx
  simpa only [Real.norm_eq_abs] using this

/-- A bound on `[0, d]` extends to `[-1/100, d + 1/100]` with the derivative bound. -/
theorem ext_bound {g g' : ℝ → ℝ} {d M B : ℝ} (hd : 0 ≤ d) (hg : ∀ t, HasDerivAt g (g' t) t)
    (hM : ∀ t ∈ Icc (-(1 / 100)) (d + 1 / 100), |g' t| ≤ M) (hB : ∀ t ∈ Icc 0 d, |g t| ≤ B)
    {τ : ℝ} (hτ : τ ∈ Icc (-(1 / 100)) (d + 1 / 100)) : |g τ| ≤ B + M / 100 := by
  have h0 : (0 : ℝ) ∈ Icc (-(1 / 100)) (d + 1 / 100) := ⟨by norm_num, by linarith⟩
  have hd' : d ∈ Icc (-(1 / 100)) (d + 1 / 100) := ⟨by linarith, by linarith⟩
  have hM0 : 0 ≤ M := le_trans (abs_nonneg _) (hM 0 h0)
  obtain ⟨hτ1, hτ2⟩ := hτ
  rcases lt_or_ge τ 0 with hl | hl
  · have hl1 := lip_of_deriv hg hM ⟨hτ1, hτ2⟩ h0
    have hb := abs_le.mp (hB 0 ⟨le_rfl, hd⟩)
    have : M * |τ - 0| ≤ M * (1 / 100) :=
      mul_le_mul_of_nonneg_left (abs_le.mpr ⟨by linarith, by linarith⟩) hM0
    have hl2 := abs_le.mp (hl1.trans this)
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  rcases le_or_gt τ d with hr | hr
  · exact (hB τ ⟨hl, hr⟩).trans (by linarith [div_nonneg hM0 (by norm_num : (0 : ℝ) ≤ 100)])
  · have hl1 := lip_of_deriv hg hM ⟨hτ1, hτ2⟩ hd'
    have hb := abs_le.mp (hB d ⟨hd, le_rfl⟩)
    have : M * |τ - d| ≤ M * (1 / 100) :=
      mul_le_mul_of_nonneg_left (abs_le.mpr ⟨by linarith, by linarith⟩) hM0
    have hl2 := abs_le.mp (hl1.trans this)
    exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- A monotone or antitone function on `[0, d]` stays between bounds of its ends. -/
theorem between {f : ℝ → ℝ} {d lo hi : ℝ} (hf : MonotoneOn f (Icc 0 d) ∨ AntitoneOn f (Icc 0 d))
    (h0 : lo ≤ f 0 ∧ f 0 ≤ hi) (hd : lo ≤ f d ∧ f d ≤ hi) {t : ℝ} (ht : t ∈ Icc 0 d) :
    lo ≤ f t ∧ f t ≤ hi := by
  have h0' : (0 : ℝ) ∈ Icc 0 d := ⟨le_rfl, ht.1.trans ht.2⟩
  have hd' : d ∈ Icc 0 d := ⟨ht.1.trans ht.2, le_rfl⟩
  rcases hf with hf | hf
  · exact ⟨h0.1.trans (hf h0' ht ht.1), (hf ht hd' ht.2).trans hd.2⟩
  · exact ⟨hd.1.trans (hf ht hd' ht.2), (hf h0' ht ht.1).trans h0.2⟩

/-- The jerk of a segment is at most its parameter in absolute value. -/
theorem Seg.jerk_abs (s : Seg) (t : ℝ) : |s.jerk t| ≤ |s.J| := by
  have hc : |1 - cos (π / s.d * t)| ≤ 2 :=
    abs_le.mpr ⟨by linarith [cos_le_one (π / s.d * t)], by linarith [neg_one_le_cos (π / s.d * t)]⟩
  have hc' : |1 - cos (π / s.d * (t + s.d))| ≤ 2 :=
    abs_le.mpr ⟨by linarith [cos_le_one (π / s.d * (t + s.d))],
      by linarith [neg_one_le_cos (π / s.d * (t + s.d))]⟩
  cases h : s.kind <;> simp only [Seg.jerk, h, cJ, iJ, dJ]
  · exact le_rfl
  · rw [abs_mul, abs_div, abs_two]; nlinarith [abs_nonneg s.J]
  · rw [abs_mul, abs_div, abs_two]; nlinarith [abs_nonneg s.J]

/-! ## The profile's nodes and segments -/

theorem prof_J (h : ProfIn Jm tj t2 t4 t15) {k : ℕ} (hk : k < 22) :
    |(prof Jm tj t2 t4 t15 k).J| ≤ 6 := by
  have h6 : |Jm| ≤ 6 := by rw [abs_of_pos h.J0]; exact h.J1
  interval_cases k <;> simp only [prof, abs_neg, abs_zero] <;> first | exact h6 | norm_num

set_option maxHeartbeats 4000000 in
/-- Node accelerations within `2`, node velocities in `[0, 3]`, and the sign of the acceleration on
each segment. -/
theorem prof_struct (h : ProfIn Jm tj t2 t4 t15) :
    (∀ k ≤ 22, |(node Jm tj t2 t4 t15 k).a| ≤ 2 ∧ 0 ≤ (node Jm tj t2 t4 t15 k).v ∧
      (node Jm tj t2 t4 t15 k).v ≤ 3) ∧
    ∀ k < 22, (∀ t ∈ Icc 0 (prof Jm tj t2 t4 t15 k).d,
        0 ≤ (prof Jm tj t2 t4 t15 k).acc (node Jm tj t2 t4 t15 k) t) ∨
      (∀ t ∈ Icc 0 (prof Jm tj t2 t4 t15 k).d,
        (prof Jm tj t2 t4 t15 k).acc (node Jm tj t2 t4 t15 k) t ≤ 0) := by
  have htj : 0 < tj := by linarith [h.tj0]
  have hJm : 0 ≤ Jm := h.J0.le
  have h2 := h.t20
  have h4 := h.t40
  have h15 := h.t150
  have hA : Jm * tj + Jm * t2 ≤ 2 := by linarith [h.A, mul_add Jm tj t2]
  have hvnn := (prof_mono hJm htj h2 h4 h15).1
  have v7 : (node Jm tj t2 t4 t15 7).v ≤ 3 := by rw [node_7_eq htj]; exact h.V
  have ok := prof_ok (Jm := Jm) htj h2 h4 h15
  obtain ⟨a1, a2, a3, a4, a5, a6, a7, a14, a15, a16, a17, a18, a19, a20, a21, a22⟩ :=
    node_a (Jm := Jm) (tj := tj) (t2 := t2) (t4 := t4) (t15 := t15)
  set N := node Jm tj t2 t4 t15 with hN
  set S := prof Jm tj t2 t4 t15 with hS
  have hNs : ∀ k, N (k + 1) = (S k).node (N k) := fun k => rfl
  have a0 : (N 0).a = 0 := rfl
  have v0 : (N 0).v = 0 := rfl
  have hJt : 0 ≤ Jm * tj / 2 := by positivity
  have hJt2 : 0 ≤ Jm * t2 := by positivity
  have hJs : ∀ k, 0 ≤ (S k).J ∨ (S k).J ≤ 0 := fun k => le_total 0 _
  have hE : ∀ k, 7 ≤ k → k < 14 → N (k + 1) = N k := by
    intro k h1 h2'
    rw [hNs]
    interval_cases k <;> simp [hS, prof, Seg.node, constNode_zero]
  have e8 : N 8 = N 7 := hE 7 le_rfl (by norm_num)
  have e9 : N 9 = N 7 := (hE 8 (by norm_num) (by norm_num)).trans e8
  have e10 : N 10 = N 7 := (hE 9 (by norm_num) (by norm_num)).trans e9
  have e11 : N 11 = N 7 := (hE 10 (by norm_num) (by norm_num)).trans e10
  have e12 : N 12 = N 7 := (hE 11 (by norm_num) (by norm_num)).trans e11
  have e13 : N 13 = N 7 := (hE 12 (by norm_num) (by norm_num)).trans e12
  have up : ∀ k, k < 7 → (N k).v ≤ (N (k + 1)).v ∧ ∀ t ∈ Set.Icc 0 (S k).d, 0 ≤ (S k).acc (N k) t := by
    intro k hk
    have hA0 : 0 ≤ (N k).a := by interval_cases k <;> simp only [a0, a1, a2, a3, a4, a5, a6] <;> positivity
    have hAd : 0 ≤ (N (k + 1)).a := by
      interval_cases k <;> simp only [a1, a2, a3, a4, a5, a6, a7, zero_add] <;> positivity
    rw [hNs] at hAd ⊢
    exact ⟨(Seg.acc_nonneg (ok k) _ (hJs k) hA0 hAd).2, (Seg.acc_nonneg (ok k) _ (hJs k) hA0 hAd).1⟩
  have dn : ∀ k, 15 ≤ k → k < 22 →
      (N (k + 1)).v ≤ (N k).v ∧ ∀ t ∈ Set.Icc 0 (S k).d, (S k).acc (N k) t ≤ 0 := by
    intro k hk1 hk2
    have hA0 : (N k).a ≤ 0 := by
      interval_cases k <;> simp only [a15, a16, a17, a18, a19, a20, a21] <;>
        first | exact le_rfl | linarith
    have hAd : (N (k + 1)).a ≤ 0 := by
      interval_cases k <;> simp only [a16, a17, a18, a19, a20, a21, a22] <;>
        first | exact le_rfl | linarith
    rw [hNs] at hAd ⊢
    exact ⟨(Seg.acc_nonpos (ok k) _ (hJs k) hA0 hAd).2, (Seg.acc_nonpos (ok k) _ (hJs k) hA0 hAd).1⟩
  have v15 : (N 15).v = (N 14).v := by
    rw [hNs]; simp only [hS, prof, Seg.node, constNode_v, a14]; ring
  have e14 : N 14 = N 7 := node_14
  obtain ⟨u0, -⟩ := up 0 (by norm_num)
  obtain ⟨u1, -⟩ := up 1 (by norm_num)
  obtain ⟨u2, -⟩ := up 2 (by norm_num)
  obtain ⟨u3, -⟩ := up 3 (by norm_num)
  obtain ⟨u4, -⟩ := up 4 (by norm_num)
  obtain ⟨u5, -⟩ := up 5 (by norm_num)
  obtain ⟨u6, -⟩ := up 6 (by norm_num)
  obtain ⟨d15, -⟩ := dn 15 le_rfl (by norm_num)
  obtain ⟨d16, -⟩ := dn 16 (by norm_num) (by norm_num)
  obtain ⟨d17, -⟩ := dn 17 (by norm_num) (by norm_num)
  obtain ⟨d18, -⟩ := dn 18 (by norm_num) (by norm_num)
  obtain ⟨d19, -⟩ := dn 19 (by norm_num) (by norm_num)
  obtain ⟨d20, -⟩ := dn 20 (by norm_num) (by norm_num)
  obtain ⟨d21, -⟩ := dn 21 (by norm_num) (by norm_num)
  have v14 : (N 14).v = (N 7).v := by rw [e14]
  have vb : ∀ k ≤ 22, (N k).v ≤ 3 := by
    intro k hk
    interval_cases k
    all_goals first
      | (simp only [v0]; norm_num)
      | (simp only [e8, e9, e10, e11, e12, e13, e14, v15]; linarith)
      | linarith
  have ab : ∀ k ≤ 22, |(N k).a| ≤ 2 := by
    intro k hk
    interval_cases k <;>
      simp only [a0, a1, a2, a3, a4, a5, a6, a7, a14, a15, a16, a17, a18, a19, a20, a21, a22, e8,
        e9, e10, e11, e12, e13, abs_neg, abs_zero] <;>
      first
        | (rw [abs_le]; constructor <;> linarith [mul_add Jm tj t2])
        | norm_num
  refine ⟨fun k hk => ⟨ab k hk, hvnn k hk, vb k hk⟩, fun k hk => ?_⟩
  by_cases h7 : k < 7
  · exact Or.inl (up k h7).2
  by_cases h15' : 15 ≤ k
  · exact Or.inr (dn k h15' hk).2
  left
  intro t ht
  have hk' : 7 ≤ k ∧ k ≤ 14 := ⟨by omega, by omega⟩
  have ha : (N k).a = 0 := by
    rcases hk' with ⟨h1, h2'⟩
    interval_cases k <;> simp only [e8, e9, e10, e11, e12, e13, e14, a7]
  have hkind : (S k).kind = .const ∧ (S k).J = 0 := by
    rcases hk' with ⟨h1, h2'⟩
    interval_cases k <;> exact ⟨rfl, rfl⟩
  simp only [Seg.acc, hkind.1, cA, hkind.2, ha, zero_mul, add_zero, le_refl]

/-- On a segment of the profile: acceleration within `2`, velocity within `3`. -/
theorem seg_in (h : ProfIn Jm tj t2 t4 t15) {k : ℕ} (hk : k < 22) {t : ℝ}
    (ht : t ∈ Icc 0 (prof Jm tj t2 t4 t15 k).d) :
    |(prof Jm tj t2 t4 t15 k).acc (node Jm tj t2 t4 t15 k) t| ≤ 2 ∧
      |(prof Jm tj t2 t4 t15 k).vel (node Jm tj t2 t4 t15 k) t| ≤ 3 := by
  have htj : 0 < tj := by linarith [h.tj0]
  have ok := prof_ok (Jm := Jm) htj h.t20 h.t40 h.t150 k
  obtain ⟨hn, hs⟩ := prof_struct h
  obtain ⟨⟨e0, v0, -⟩, ⟨ed, vd, -⟩⟩ := (prof Jm tj t2 t4 t15 k).ends ok (node Jm tj t2 t4 t15 k)
  have nk := hn k hk.le
  have nk1 : |((prof Jm tj t2 t4 t15 k).node (node Jm tj t2 t4 t15 k)).a| ≤ 2 ∧
      0 ≤ ((prof Jm tj t2 t4 t15 k).node (node Jm tj t2 t4 t15 k)).v ∧
      ((prof Jm tj t2 t4 t15 k).node (node Jm tj t2 t4 t15 k)).v ≤ 3 := hn (k + 1) hk
  have hacc : MonotoneOn ((prof Jm tj t2 t4 t15 k).acc (node Jm tj t2 t4 t15 k))
      (Icc 0 (prof Jm tj t2 t4 t15 k).d) ∨
      AntitoneOn ((prof Jm tj t2 t4 t15 k).acc (node Jm tj t2 t4 t15 k))
      (Icc 0 (prof Jm tj t2 t4 t15 k).d) := by
    rcases le_total 0 (prof Jm tj t2 t4 t15 k).J with hJ | hJ
    · exact Or.inl (monoOn_of_hasDeriv (Seg.deriv_acc ok _)
        (fun t _ => ((prof Jm tj t2 t4 t15 k).jerk_sign t).1 hJ))
    · exact Or.inr (antiOn_of_hasDeriv (Seg.deriv_acc ok _)
        (fun t _ => ((prof Jm tj t2 t4 t15 k).jerk_sign t).2 hJ))
  have hvel : MonotoneOn ((prof Jm tj t2 t4 t15 k).vel (node Jm tj t2 t4 t15 k))
      (Icc 0 (prof Jm tj t2 t4 t15 k).d) ∨
      AntitoneOn ((prof Jm tj t2 t4 t15 k).vel (node Jm tj t2 t4 t15 k))
      (Icc 0 (prof Jm tj t2 t4 t15 k).d) := by
    rcases hs k hk with hA | hA
    · exact Or.inl (monoOn_of_hasDeriv (Seg.deriv_vel ok _) hA)
    · exact Or.inr (antiOn_of_hasDeriv (Seg.deriv_vel ok _) hA)
  constructor
  · have := between (lo := -2) (hi := 2) hacc (by rw [e0]; exact abs_le.mp nk.1)
      (by rw [ed]; exact abs_le.mp nk1.1) ht
    exact abs_le.mpr this
  · have := between (lo := 0) (hi := 3) hvel (by rw [v0]; exact ⟨nk.2.1, nk.2.2⟩)
      (by rw [vd]; exact ⟨nk1.2.1, nk1.2.2⟩) ht
    exact abs_le.mpr ⟨by linarith [this.1], this.2⟩


/-! ## Start times, clamps and partial sums -/

theorem prof_d_nonneg (h : ProfIn Jm tj t2 t4 t15) (k : ℕ) : 0 ≤ (prof Jm tj t2 t4 t15 k).d :=
  (prof_ok (by linarith [h.tj0]) h.t20 h.t40 h.t150 k).d_nonneg

theorem tEnd_succ (k : ℕ) :
    tEnd Jm tj t2 t4 t15 (k + 1) = tEnd Jm tj t2 t4 t15 k + (prof Jm tj t2 t4 t15 k).d := rfl

theorem tEnd_mono (h : ProfIn Jm tj t2 t4 t15) : Monotone (tEnd Jm tj t2 t4 t15) :=
  monotone_nat_of_le_succ fun k => by rw [tEnd_succ]; linarith [prof_d_nonneg h k]

theorem tEnd_nonneg (h : ProfIn Jm tj t2 t4 t15) (k : ℕ) : 0 ≤ tEnd Jm tj t2 t4 t15 k :=
  tEnd_mono h (Nat.zero_le k)

/-- The clamped local time of segment `k`. -/
def clampT (Jm tj t2 t4 t15 : ℝ) (k : ℕ) (t : ℝ) : ℝ :=
  max 0 (min (t - tEnd Jm tj t2 t4 t15 k) (prof Jm tj t2 t4 t15 k).d)

theorem segAt_eq (k : ℕ) (t : ℝ) :
    segAt Jm tj t2 t4 t15 k t =
      (prof Jm tj t2 t4 t15 k).pos (node Jm tj t2 t4 t15 k) (clampT Jm tj t2 t4 t15 k t) := rfl

theorem clamp_before (h : ProfIn Jm tj t2 t4 t15) {k : ℕ} {t : ℝ}
    (ht : t ≤ tEnd Jm tj t2 t4 t15 k) : clampT Jm tj t2 t4 t15 k t = 0 := by
  have := prof_d_nonneg h k
  unfold clampT; simp only [max_def, min_def]; split_ifs <;> linarith

theorem clamp_after (h : ProfIn Jm tj t2 t4 t15) {k : ℕ} {t : ℝ}
    (ht : tEnd Jm tj t2 t4 t15 (k + 1) ≤ t) :
    clampT Jm tj t2 t4 t15 k t = (prof Jm tj t2 t4 t15 k).d := by
  have := prof_d_nonneg h k
  rw [tEnd_succ] at ht
  unfold clampT; simp only [max_def, min_def]; split_ifs <;> linarith

theorem clamp_mem (h : ProfIn Jm tj t2 t4 t15) (k : ℕ) (t : ℝ) :
    clampT Jm tj t2 t4 t15 k t ∈ Icc 0 (prof Jm tj t2 t4 t15 k).d := by
  have := prof_d_nonneg h k
  unfold clampT; simp only [max_def, min_def]
  split_ifs <;> constructor <;> linarith

theorem clamp_mono (k : ℕ) : Monotone (clampT Jm tj t2 t4 t15 k) := fun a b hab => by
  unfold clampT
  exact max_le_max le_rfl (min_le_min (by linarith) le_rfl)

theorem clamp_in {k : ℕ} {τ : ℝ} (hτ : τ ∈ Icc 0 (prof Jm tj t2 t4 t15 k).d) :
    clampT Jm tj t2 t4 t15 k (tEnd Jm tj t2 t4 t15 k + τ) = τ := by
  obtain ⟨h1, h2⟩ := hτ
  unfold clampT; rw [add_sub_cancel_left, min_eq_left h2, max_eq_right h1]

theorem inc_before (h : ProfIn Jm tj t2 t4 t15) {k : ℕ} {t : ℝ}
    (ht : t ≤ tEnd Jm tj t2 t4 t15 k) :
    segAt Jm tj t2 t4 t15 k t - (node Jm tj t2 t4 t15 k).p = 0 := by
  have ok := prof_ok (Jm := Jm) (tj := tj) (by linarith [h.tj0]) h.t20 h.t40 h.t150 k
  rw [segAt_eq, clamp_before h ht, (Seg.ends ok _).1.2.2, sub_self]

theorem inc_after (h : ProfIn Jm tj t2 t4 t15) {k : ℕ} {t : ℝ}
    (ht : tEnd Jm tj t2 t4 t15 (k + 1) ≤ t) :
    segAt Jm tj t2 t4 t15 k t - (node Jm tj t2 t4 t15 k).p =
      (node Jm tj t2 t4 t15 (k + 1)).p - (node Jm tj t2 t4 t15 k).p := by
  have ok := prof_ok (Jm := Jm) (tj := tj) (by linarith [h.tj0]) h.t20 h.t40 h.t150 k
  rw [segAt_eq, clamp_after h ht, (Seg.ends ok _).2.2.2]
  rfl

/-- Past the start of segment `n`, the first `n` increments sum to node `n`. -/
theorem sum_full (h : ProfIn Jm tj t2 t4 t15) : ∀ (n : ℕ) (t : ℝ), tEnd Jm tj t2 t4 t15 n ≤ t →
    ∑ j ∈ Finset.range n, (segAt Jm tj t2 t4 t15 j t - (node Jm tj t2 t4 t15 j).p) =
      (node Jm tj t2 t4 t15 n).p
  | 0, t, _ => by simp [node]
  | n + 1, t, ht => by
    rw [Finset.sum_range_succ, sum_full h n t ((tEnd_mono h (Nat.le_succ n)).trans ht),
      inc_after h ht]
    ring

/-- Before the start of segment `m`, the later increments vanish. -/
theorem sum_stop (h : ProfIn Jm tj t2 t4 t15) {m : ℕ} {t : ℝ} (ht : t ≤ tEnd Jm tj t2 t4 t15 m)
    (n : ℕ) (hn : m ≤ n) :
    ∑ j ∈ Finset.range n, (segAt Jm tj t2 t4 t15 j t - (node Jm tj t2 t4 t15 j).p) =
      ∑ j ∈ Finset.range m, (segAt Jm tj t2 t4 t15 j t - (node Jm tj t2 t4 t15 j).p) := by
  induction n, hn using Nat.le_induction with
  | base => rfl
  | succ n hmn ih =>
    rw [Finset.sum_range_succ, ih, inc_before h (ht.trans (tEnd_mono h hmn)), add_zero]

/-- The clamped local times sum to the clamped time. -/
theorem clamp_sum (h : ProfIn Jm tj t2 t4 t15) : ∀ (n : ℕ) (t : ℝ),
    ∑ j ∈ Finset.range n, clampT Jm tj t2 t4 t15 j t = max 0 (min t (tEnd Jm tj t2 t4 t15 n))
  | 0, t => by
    simp only [Finset.range_zero, Finset.sum_empty]
    show (0 : ℝ) = max 0 (min t 0)
    simp only [max_def, min_def]; split_ifs <;> linarith
  | n + 1, t => by
    rw [Finset.sum_range_succ, clamp_sum h n t, tEnd_succ]
    have := tEnd_nonneg h n
    have := prof_d_nonneg h n
    unfold clampT; simp only [max_def, min_def]; split_ifs <;> linarith

/-- A segment of the profile is `3`-Lipschitz on `[0, d]`. -/
theorem seg_lip3 (h : ProfIn Jm tj t2 t4 t15) {k : ℕ} (hk : k < 22) {x y : ℝ}
    (hx : x ∈ Icc 0 (prof Jm tj t2 t4 t15 k).d) (hy : y ∈ Icc 0 (prof Jm tj t2 t4 t15 k).d) :
    |(prof Jm tj t2 t4 t15 k).pos (node Jm tj t2 t4 t15 k) x -
      (prof Jm tj t2 t4 t15 k).pos (node Jm tj t2 t4 t15 k) y| ≤ 3 * |x - y| := by
  have ok := prof_ok (Jm := Jm) (tj := tj) (by linarith [h.tj0]) h.t20 h.t40 h.t150 k
  exact lip_of_deriv (Seg.deriv_pos ok _) (fun t ht => (seg_in h hk ht).2) hx hy

/-! ## Sensitivity of the ramps to the duration -/

/-- The duration-dependent part of a ramp's position. -/
def rampF (d τ : ℝ) : ℝ := -(d / π) ^ 2 * τ + (d / π) ^ 3 * sin (π / d * τ)

theorem iP_eq (n : Node) (J d τ : ℝ) :
    iP n J (π / d) τ =
      n.p + n.v * τ + n.a * τ ^ 2 / 2 + J / 2 * τ ^ 3 / 6 + J / 2 * rampF d τ := by
  have hπ := pi_pos.ne'
  simp only [iP, rampF]; field_simp; ring

theorem dP_eq (n : Node) (J d τ : ℝ) (hd : d ≠ 0) :
    dP n J (π / d) d τ =
      n.p + n.v * τ + n.a * τ ^ 2 / 2 + J / 2 * τ ^ 3 / 6 - J / 2 * rampF d τ := by
  have hπ := pi_pos.ne'
  have hs : sin (π / d * (τ + d)) = -sin (π / d * τ) := by
    rw [show π / d * (τ + d) = π / d * τ + π by field_simp, sin_add_pi]
  simp only [dP, rampF, rAT, rVT, rPT, hs]; field_simp; ring

/-- The core estimate of `rampF_lip`, with `x = 1/π`. -/
theorem sens_core {x d d' τ s s' : ℝ} (hx0 : 0 < x) (hx : x ≤ 1 / 3) (hd1 : 1 / 300 ≤ d)
    (hd2 : d ≤ 1 / 4) (hdd : |d' - d| ≤ 1 / 1000) (hτ0 : 0 ≤ τ) (hτ : τ ≤ 2 * d)
    (hs' : |s'| ≤ 1) (hss : |s' - s| ≤ 4 * τ * |d' - d| / (d * d')) :
    |(d' - d) * (-(d' + d) * x ^ 2 * τ + (d' ^ 2 + d' * d + d ^ 2) * x ^ 3 * s') +
      d ^ 3 * x ^ 3 * (s' - s)| ≤ 1 / 3 * |d' - d| := by
  obtain ⟨hdd1, hdd2⟩ := abs_le.mp hdd
  have hd0 : 0 < d := by linarith
  have hd'0 : 0 < d' := by linarith
  have hd'7 : 7 / 10 * d ≤ d' := by linarith
  have hx2 : x ^ 2 ≤ 1 / 9 := by nlinarith
  have hx3 : x ^ 3 ≤ 1 / 27 := by nlinarith
  have hx30 : 0 ≤ x ^ 3 := by positivity
  have hsum : d' + d ≤ 501 / 1000 := by linarith
  have p1 : (d' + d) * x ^ 2 * τ ≤ 501 / 1000 * (1 / 9) * (1 / 2) :=
    mul_le_mul (mul_le_mul hsum hx2 (sq_nonneg _) (by norm_num)) (by linarith) hτ0 (by norm_num)
  have p1' : 0 ≤ (d' + d) * x ^ 2 * τ := mul_nonneg (mul_nonneg (by linarith) (sq_nonneg _)) hτ0
  have hQ : d' ^ 2 + d' * d + d ^ 2 ≤ 3 * (251 / 1000) ^ 2 := by nlinarith
  have hQ0 : 0 ≤ d' ^ 2 + d' * d + d ^ 2 := by nlinarith
  have p2 : (d' ^ 2 + d' * d + d ^ 2) * x ^ 3 ≤ 3 * (251 / 1000) ^ 2 * (1 / 27) :=
    mul_le_mul hQ hx3 hx30 (by norm_num)
  have p20 : 0 ≤ (d' ^ 2 + d' * d + d ^ 2) * x ^ 3 := mul_nonneg hQ0 hx30
  obtain ⟨hs1, hs2⟩ := abs_le.mp hs'
  have q1 : 0 ≤ (d' ^ 2 + d' * d + d ^ 2) * x ^ 3 * (1 - s') := mul_nonneg p20 (by linarith)
  have q2 : 0 ≤ (d' ^ 2 + d' * d + d ^ 2) * x ^ 3 * (1 + s') := mul_nonneg p20 (by linarith)
  have hC : |-(d' + d) * x ^ 2 * τ + (d' ^ 2 + d' * d + d ^ 2) * x ^ 3 * s'| ≤ 1 / 20 := by
    rw [abs_le]; constructor <;> linarith
  have T1 : |(d' - d) * (-(d' + d) * x ^ 2 * τ + (d' ^ 2 + d' * d + d ^ 2) * x ^ 3 * s')| ≤
      |d' - d| * (1 / 20) := by
    rw [abs_mul]; exact mul_le_mul_of_nonneg_left hC (abs_nonneg _)
  have hD := abs_nonneg (d' - d)
  have hdx : 0 ≤ d ^ 3 * x ^ 3 := by positivity
  have r1 : x ^ 3 * τ ≤ 1 / 27 * (2 * d) := mul_le_mul hx3 hτ hτ0 (by norm_num)
  have r2 : d ^ 2 ≤ 1 / 16 := by nlinarith
  have r3 : d ^ 2 * (x ^ 3 * τ) ≤ d ^ 2 * (1 / 27 * (2 * d)) :=
    mul_le_mul_of_nonneg_left r1 (sq_nonneg d)
  have r4 : d * d ^ 2 ≤ d * (1 / 16) := mul_le_mul_of_nonneg_left r2 hd0.le
  have r5 : 4 * d ^ 2 * x ^ 3 * τ / d' ≤ 1 / 30 := by
    rw [div_le_iff₀ hd'0]; nlinarith
  have T2 : |d ^ 3 * x ^ 3 * (s' - s)| ≤ |d' - d| * (1 / 30) := by
    rw [abs_mul, abs_of_nonneg hdx]
    calc d ^ 3 * x ^ 3 * |s' - s| ≤ d ^ 3 * x ^ 3 * (4 * τ * |d' - d| / (d * d')) :=
          mul_le_mul_of_nonneg_left hss hdx
      _ = |d' - d| * (4 * d ^ 2 * x ^ 3 * τ / d') := by field_simp
      _ ≤ |d' - d| * (1 / 30) := mul_le_mul_of_nonneg_left r5 hD
  have := abs_add_le ((d' - d) * (-(d' + d) * x ^ 2 * τ + (d' ^ 2 + d' * d + d ^ 2) * x ^ 3 * s'))
    (d ^ 3 * x ^ 3 * (s' - s))
  linarith

/-- The duration-dependent part of a ramp is `1/3`-Lipschitz in the duration. -/
theorem rampF_lip {d d' τ : ℝ} (hd1 : 1 / 300 ≤ d) (hd2 : d ≤ 1 / 4) (hdd : |d' - d| ≤ 1 / 1000)
    (hτ0 : 0 ≤ τ) (hτ : τ ≤ 2 * d) : |rampF d' τ - rampF d τ| ≤ 1 / 3 * |d' - d| := by
  obtain ⟨hdd1, hdd2⟩ := abs_le.mp hdd
  have hd0 : 0 < d := by linarith
  have hd'0 : 0 < d' := by linarith
  have hπ0 := pi_pos
  have hx0 : 0 < π⁻¹ := inv_pos.mpr hπ0
  have hx : π⁻¹ ≤ 1 / 3 := by
    rw [inv_le_comm₀ hπ0 (by norm_num)]; norm_num; linarith [pi_gt_three]
  have hss : |sin (π / d' * τ) - sin (π / d * τ)| ≤ 4 * τ * |d' - d| / (d * d') := by
    refine (abs_sin_sub_sin_le _ _).trans ?_
    have e : π / d' * τ - π / d * τ = π * τ / (d * d') * (d - d') := by field_simp
    rw [e, abs_mul, abs_of_nonneg (by positivity), abs_sub_comm d d']
    have h4 : π * τ / (d * d') ≤ 4 * τ / (d * d') :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right pi_le_four hτ0) (mul_pos hd0 hd'0).le
    calc π * τ / (d * d') * |d' - d| ≤ 4 * τ / (d * d') * |d' - d| :=
          mul_le_mul_of_nonneg_right h4 (abs_nonneg _)
      _ = 4 * τ * |d' - d| / (d * d') := by ring
  have e : rampF d' τ - rampF d τ =
      (d' - d) * (-(d' + d) * π⁻¹ ^ 2 * τ + (d' ^ 2 + d' * d + d ^ 2) * π⁻¹ ^ 3 *
        sin (π / d' * τ)) + d ^ 3 * π⁻¹ ^ 3 * (sin (π / d' * τ) - sin (π / d * τ)) := by
    simp only [rampF, div_eq_mul_inv d, div_eq_mul_inv d']; ring
  rw [e]
  exact sens_core hx0 hx hd1 hd2 hdd hτ0 hτ (abs_sin_le_one _) hss

theorem tri4 (X1 X2 X3 τ R : ℝ) (hτ : 0 ≤ τ) :
    |X1 + X2 * τ + X3 * τ ^ 2 / 2 + R| ≤ |X1| + |X2| * τ + |X3| * τ ^ 2 / 2 + |R| := by
  have a1 := abs_add_le (X1 + X2 * τ + X3 * τ ^ 2 / 2) R
  have a2 := abs_add_le (X1 + X2 * τ) (X3 * τ ^ 2 / 2)
  have a3 := abs_add_le X1 (X2 * τ)
  have b1 : |X2 * τ| = |X2| * τ := by rw [abs_mul, abs_of_nonneg hτ]
  have b2 : |X3 * τ ^ 2 / 2| = |X3| * τ ^ 2 / 2 := by
    rw [abs_div, abs_mul, abs_of_nonneg (sq_nonneg τ), abs_two]
  linarith

/-- The profile is monotone. -/
theorem profPos_mono (h : ProfIn Jm tj t2 t4 t15) : Monotone (profPos Jm tj t2 t4 t15) := by
  have hmono := (prof_mono h.J0.le (by linarith [h.tj0]) h.t20 h.t40 h.t150).2
  intro a b hab
  unfold profPos
  refine Finset.sum_le_sum fun j hj => ?_
  have hj' : j < 22 := Finset.mem_range.mp hj
  rw [segAt_eq, segAt_eq]
  have := (hmono j hj').2 (clamp_mem h j a) (clamp_mem h j b) (clamp_mono j hab)
  linarith

/-- The profile starts at `0` (for `t ≤ 0`). -/
theorem profPos_of_le (h : ProfIn Jm tj t2 t4 t15) {t : ℝ} (ht : t ≤ 0) :
    profPos Jm tj t2 t4 t15 t = 0 := by
  unfold profPos
  rw [sum_stop h (m := 0) ht 22 (by norm_num)]
  simp

/-- The profile ends at the end node (for `t ≥ tEnd 22`). -/
theorem profPos_of_ge (h : ProfIn Jm tj t2 t4 t15) {t : ℝ} (ht : tEnd Jm tj t2 t4 t15 22 ≤ t) :
    profPos Jm tj t2 t4 t15 t = (node Jm tj t2 t4 t15 22).p := by
  exact sum_full h 22 t ht

/-- On segment `k` the profile is the segment's closed form. -/
theorem profPos_seg (h : ProfIn Jm tj t2 t4 t15) {k : ℕ} (hk : k < 22) {τ : ℝ}
    (hτ : τ ∈ Set.Icc 0 (prof Jm tj t2 t4 t15 k).d) :
    profPos Jm tj t2 t4 t15 (tEnd Jm tj t2 t4 t15 k + τ) =
      (prof Jm tj t2 t4 t15 k).pos (node Jm tj t2 t4 t15 k) τ := by
  unfold profPos
  have hle : tEnd Jm tj t2 t4 t15 k + τ ≤ tEnd Jm tj t2 t4 t15 (k + 1) := by
    rw [tEnd_succ]; linarith [hτ.2]
  rw [sum_stop h hle 22 hk, Finset.sum_range_succ,
    sum_full h k _ (by linarith [hτ.1]), segAt_eq, clamp_in hτ]
  ring

/-- The profile is `3`-Lipschitz. -/
theorem profPos_lip (h : ProfIn Jm tj t2 t4 t15) (t t' : ℝ) :
    |profPos Jm tj t2 t4 t15 t - profPos Jm tj t2 t4 t15 t'| ≤ 3 * |t - t'| := by
  -- for `s ≤ s'`
  have key : ∀ s s' : ℝ, s ≤ s' →
      |profPos Jm tj t2 t4 t15 s - profPos Jm tj t2 t4 t15 s'| ≤ 3 * |s - s'| := by
    intro s s' hss
    have hm := profPos_mono h hss
    have hsum : profPos Jm tj t2 t4 t15 s' - profPos Jm tj t2 t4 t15 s ≤
        3 * (∑ j ∈ Finset.range 22, clampT Jm tj t2 t4 t15 j s' -
          ∑ j ∈ Finset.range 22, clampT Jm tj t2 t4 t15 j s) := by
      unfold profPos
      rw [← Finset.sum_sub_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_le_sum fun j hj => ?_
      have hj' : j < 22 := Finset.mem_range.mp hj
      rw [segAt_eq, segAt_eq]
      have h1 := seg_lip3 h hj' (clamp_mem h j s') (clamp_mem h j s)
      have h2 := clamp_mono (Jm := Jm) (tj := tj) (t2 := t2) (t4 := t4) (t15 := t15) j hss
      rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ clampT Jm tj t2 t4 t15 j s' -
        clampT Jm tj t2 t4 t15 j s)] at h1
      linarith [(abs_le.mp h1).2]
    rw [clamp_sum h, clamp_sum h] at hsum
    have hc : max 0 (min s' (tEnd Jm tj t2 t4 t15 22)) - max 0 (min s (tEnd Jm tj t2 t4 t15 22)) ≤
        s' - s := by
      simp only [max_def, min_def]; split_ifs <;> linarith
    rw [abs_sub_comm, abs_of_nonneg (by linarith), abs_sub_comm, abs_of_nonneg (by linarith)]
    linarith
  rcases le_total t t' with ht | ht
  · exact key t t' ht
  · rw [abs_sub_comm, abs_sub_comm t]; exact key t' t ht

/-- The node values: accelerations within `2`, velocities in `[0, 3]`. -/
theorem node_bounds (h : ProfIn Jm tj t2 t4 t15) {k : ℕ} (hk : k ≤ 22) :
    |(node Jm tj t2 t4 t15 k).a| ≤ 2 ∧ 0 ≤ (node Jm tj t2 t4 t15 k).v ∧
      (node Jm tj t2 t4 t15 k).v ≤ 3 := by
  exact (prof_struct h).1 k hk

/-- The segment durations and start times. -/
theorem prof_d (h : ProfIn Jm tj t2 t4 t15) {k : ℕ} (hk : k < 22) :
    0 ≤ (prof Jm tj t2 t4 t15 k).d ∧ (0 ≤ tEnd Jm tj t2 t4 t15 k) ∧
      tEnd Jm tj t2 t4 t15 (k + 1) = tEnd Jm tj t2 t4 t15 k + (prof Jm tj t2 t4 t15 k).d := by
  clear hk
  exact ⟨prof_d_nonneg h k, tEnd_nonneg h k, rfl⟩

/-- A segment's closed form, extended by up to `1/100` beyond its ends, is `4`-Lipschitz. -/
theorem seg_lip (h : ProfIn Jm tj t2 t4 t15) {k : ℕ} (hk : k < 22) {τ τ' : ℝ}
    (hτ : τ ∈ Set.Icc (-(1 / 100)) ((prof Jm tj t2 t4 t15 k).d + 1 / 100))
    (hτ' : τ' ∈ Set.Icc (-(1 / 100)) ((prof Jm tj t2 t4 t15 k).d + 1 / 100)) :
    |(prof Jm tj t2 t4 t15 k).pos (node Jm tj t2 t4 t15 k) τ -
      (prof Jm tj t2 t4 t15 k).pos (node Jm tj t2 t4 t15 k) τ'| ≤ 4 * |τ - τ'| := by
  have ok := prof_ok (Jm := Jm) (tj := tj) (by linarith [h.tj0]) h.t20 h.t40 h.t150 k
  have hd := prof_d_nonneg h k
  have hJ := prof_J h hk
  have hacc : ∀ t ∈ Icc (-(1 / 100)) ((prof Jm tj t2 t4 t15 k).d + 1 / 100),
      |(prof Jm tj t2 t4 t15 k).acc (node Jm tj t2 t4 t15 k) t| ≤ 2 + 6 / 100 :=
    fun t ht => ext_bound hd (Seg.deriv_acc ok _)
      (fun t _ => ((prof Jm tj t2 t4 t15 k).jerk_abs t).trans hJ) (fun t ht => (seg_in h hk ht).1) ht
  have hvel : ∀ t ∈ Icc (-(1 / 100)) ((prof Jm tj t2 t4 t15 k).d + 1 / 100),
      |(prof Jm tj t2 t4 t15 k).vel (node Jm tj t2 t4 t15 k) t| ≤ 4 :=
    fun t ht => (ext_bound hd (Seg.deriv_vel ok _) hacc (fun t ht => (seg_in h hk ht).2) ht).trans
      (by norm_num)
  exact lip_of_deriv (Seg.deriv_pos ok _) hvel hτ hτ'

/-- **A segment's closed form slightly outside the segment** stays within `8` times the distance
to the segment of the profile. -/
theorem seg_ext (h : ProfIn Jm tj t2 t4 t15) {k : ℕ} (hk : k < 22) {τ : ℝ}
    (hτ : τ ∈ Set.Icc (-(1 / 100)) ((prof Jm tj t2 t4 t15 k).d + 1 / 100)) :
    |(prof Jm tj t2 t4 t15 k).pos (node Jm tj t2 t4 t15 k) τ -
      profPos Jm tj t2 t4 t15 (tEnd Jm tj t2 t4 t15 k + τ)| ≤
      8 * (max (-τ) 0 + max (τ - (prof Jm tj t2 t4 t15 k).d) 0) := by
  have hd := prof_d_nonneg h k
  obtain ⟨hτ1, hτ2⟩ := hτ
  have hm1 := le_max_right (-τ) 0
  have hm2 := le_max_right (τ - (prof Jm tj t2 t4 t15 k).d) 0
  rcases lt_or_ge τ 0 with hl | hl
  · have e0 := profPos_seg h hk (τ := 0) ⟨le_rfl, hd⟩
    rw [add_zero] at e0
    have l1 := seg_lip h hk ⟨hτ1, hτ2⟩ (τ' := 0) ⟨by norm_num, by linarith⟩
    have l2 := profPos_lip h (tEnd Jm tj t2 t4 t15 k + τ) (tEnd Jm tj t2 t4 t15 k)
    rw [e0, add_sub_cancel_left, abs_of_neg hl] at l2
    rw [sub_zero, abs_of_neg hl] at l1
    rw [max_eq_left (by linarith : (0 : ℝ) ≤ -τ), max_eq_right (by linarith : τ - _ ≤ 0)]
    have := abs_le.mp l1
    have := abs_le.mp l2
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  rcases le_or_gt τ (prof Jm tj t2 t4 t15 k).d with hr | hr
  · rw [profPos_seg h hk ⟨hl, hr⟩, sub_self, abs_zero]; linarith
  · have e0 := profPos_seg h hk (τ := (prof Jm tj t2 t4 t15 k).d) ⟨hd, le_rfl⟩
    have l1 := seg_lip h hk ⟨hτ1, hτ2⟩ (τ' := (prof Jm tj t2 t4 t15 k).d) ⟨by linarith, by linarith⟩
    have l2 := profPos_lip h (tEnd Jm tj t2 t4 t15 k + τ)
      (tEnd Jm tj t2 t4 t15 k + (prof Jm tj t2 t4 t15 k).d)
    rw [e0, add_sub_add_left_eq_sub, abs_of_pos (by linarith : (0 : ℝ) < τ - _)] at l2
    rw [abs_of_pos (by linarith : (0 : ℝ) < τ - _)] at l1
    rw [max_eq_right (by linarith : -τ ≤ 0), max_eq_left (by linarith : (0 : ℝ) ≤ τ - _)]
    have := abs_le.mp l1
    have := abs_le.mp l2
    exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- **The closed forms depend Lipschitz-continuously on the start node and the duration**: for a
ramp of duration `d ∈ [1/300, 1/4]` (and `d'` within `1/1000` of it), jerk `|J| ≤ 6`, at local time
`τ ∈ [0, 2d]`; for a constant-jerk segment at any `τ ≥ 0` (the duration does not enter). -/
theorem seg_sens (kind : Kind) {J d d' τ : ℝ} (n n' : Node) (hJ : |J| ≤ 6)
    (hd : kind ≠ .const → 1 / 300 ≤ d ∧ d ≤ 1 / 4 ∧ |d' - d| ≤ 1 / 1000 ∧ τ ≤ 2 * d)
    (hτ : 0 ≤ τ) :
    |Seg.pos ⟨kind, J, d'⟩ n' τ - Seg.pos ⟨kind, J, d⟩ n τ| ≤
      |n'.p - n.p| + |n'.v - n.v| * τ + |n'.a - n.a| * τ ^ 2 / 2 + 2 * |d' - d| := by
  have hD := abs_nonneg (d' - d)
  have hne : ∀ k : Kind, k ≠ .const → 1 / 300 ≤ d ∧ d ≤ 1 / 4 ∧ |d' - d| ≤ 1 / 1000 ∧ τ ≤ 2 * d →
      d ≠ 0 ∧ d' ≠ 0 ∧ |J / 2 * (rampF d' τ - rampF d τ)| ≤ |d' - d| := by
    intro _ _ ⟨hd1, hd2, hdd, hτ2⟩
    obtain ⟨hdd1, -⟩ := abs_le.mp hdd
    refine ⟨by linarith, by linarith, ?_⟩
    have hF := rampF_lip hd1 hd2 hdd hτ hτ2
    rw [abs_mul, abs_div, abs_two]
    have := mul_le_mul hJ hF (abs_nonneg _) (by norm_num)
    linarith
  cases kind with
  | const =>
    simp only [Seg.pos, cP]
    have e : n'.p + n'.v * τ + n'.a * τ ^ 2 / 2 + J * τ ^ 3 / 6 -
        (n.p + n.v * τ + n.a * τ ^ 2 / 2 + J * τ ^ 3 / 6) =
        (n'.p - n.p) + (n'.v - n.v) * τ + (n'.a - n.a) * τ ^ 2 / 2 + 0 := by ring
    rw [e]
    have := tri4 (n'.p - n.p) (n'.v - n.v) (n'.a - n.a) τ 0 hτ
    rw [abs_zero] at this
    linarith
  | incr =>
    obtain ⟨hd0, hd'0, hR⟩ := hne .incr (by intro h; cases h) (hd (by intro h; cases h))
    simp only [Seg.pos]
    rw [iP_eq, iP_eq]
    have e : n'.p + n'.v * τ + n'.a * τ ^ 2 / 2 + J / 2 * τ ^ 3 / 6 + J / 2 * rampF d' τ -
        (n.p + n.v * τ + n.a * τ ^ 2 / 2 + J / 2 * τ ^ 3 / 6 + J / 2 * rampF d τ) =
        (n'.p - n.p) + (n'.v - n.v) * τ + (n'.a - n.a) * τ ^ 2 / 2 +
          J / 2 * (rampF d' τ - rampF d τ) := by ring
    rw [e]
    have := tri4 (n'.p - n.p) (n'.v - n.v) (n'.a - n.a) τ (J / 2 * (rampF d' τ - rampF d τ)) hτ
    linarith
  | decr =>
    obtain ⟨hd0, hd'0, hR⟩ := hne .decr (by intro h; cases h) (hd (by intro h; cases h))
    simp only [Seg.pos]
    rw [dP_eq _ _ _ _ hd'0, dP_eq _ _ _ _ hd0]
    have e : n'.p + n'.v * τ + n'.a * τ ^ 2 / 2 + J / 2 * τ ^ 3 / 6 - J / 2 * rampF d' τ -
        (n.p + n.v * τ + n.a * τ ^ 2 / 2 + J / 2 * τ ^ 3 / 6 - J / 2 * rampF d τ) =
        (n'.p - n.p) + (n'.v - n.v) * τ + (n'.a - n.a) * τ ^ 2 / 2 +
          -(J / 2 * (rampF d' τ - rampF d τ)) := by ring
    rw [e]
    have := tri4 (n'.p - n.p) (n'.v - n.v) (n'.a - n.a) τ (-(J / 2 * (rampF d' τ - rampF d τ))) hτ
    rw [abs_neg] at this
    linarith

end

end Contracts.Mission.SC
