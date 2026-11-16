import Contracts.Mission.SCurveTable
import Contracts.Mission.SCurveGlueLoop
import Contracts.Mission.SCurveGlueReal

/-!
# Glue for `SCurve::get_jerk_accel_vel_pos_at_time`: the cases of the selected index

For each index `k` the loop can select, the position `postP S t k` the code evaluates is within
`3/2000` of the profile: `k = 0` (time before the first end time), `k = j + 1 ∈ 1 … 22` (time in
segment `k`, by kind), `k = 23` (time after the last end time).
-/

namespace Contracts.Mission

open Float.Model UnpackedFloat AC_WPNav_lib

noncomputable section

namespace SCG

/-- Rounded difference of two finite floats `b ≤ a` not too far apart. -/
theorem sub_fl {a b : Float32} (fa : a.IsFinite) (fb : b.IsFinite) (hab : b.toReal ≤ a.toReal)
    (h1 : a.toReal - b.toReal ≤ 2 ^ 11) :
    (a - b).IsFinite ∧ |(a - b).toReal - (a.toReal - b.toReal)| ≤
      1 / 16777216 * (a.toReal - b.toReal) := by
  have hm := sce_max
  obtain ⟨hf, he⟩ := Float32.sub_err_all fa fb (by rw [abs_of_nonneg (by linarith)]; linarith)
  rw [abs_of_nonneg (by linarith : (0 : ℝ) ≤ a.toReal - b.toReal),
    show (2 : ℝ) ^ (-24 : ℤ) = 1 / 16777216 by norm_num] at he
  exact ⟨hf, he⟩

/-- **Constant-jerk segment in `float`**, from numeric bounds on the inputs. -/
theorem const_float {τ J0 A0 V0 P0 : Float32} {n : SC.Node} {Jr d : ℝ} (fτ : τ.IsFinite)
    (fJ : J0.IsFinite) (fA : A0.IsFinite) (fV : V0.IsFinite) (fP : P0.IsFinite)
    (hτ0 : 0 ≤ τ.toReal) (hτ1 : τ.toReal ≤ 1024) (hJ : J0.toReal = Jr) (hJ6 : |Jr| ≤ 6)
    (hab : |A0.toReal| ≤ 3) (hp : |P0.toReal| ≤ 5) (hv : |V0.toReal| * τ.toReal ≤ 46)
    (ha : |A0.toReal| * τ.toReal ^ 2 ≤ 19) (hj : |Jr| * τ.toReal ^ 3 ≤ 1)
    (ep : |P0.toReal - n.p| ≤ 4 / 10 ^ 4) (ev : |V0.toReal - n.v| * τ.toReal ≤ 46 / 10 ^ 5)
    (ea : |A0.toReal - n.a| * τ.toReal ^ 2 ≤ 1 / 10 ^ 4) :
    (SCurve.calc_javp_for_segment_const_jerk τ J0 A0 V0 P0 0.0 0.0 0.0 0.0).2.2.2.IsFinite ∧
      |(SCurve.calc_javp_for_segment_const_jerk τ J0 A0 V0 P0 0.0 0.0 0.0 0.0).2.2.2.toReal -
        SC.Seg.pos ⟨.const, Jr, d⟩ n τ.toReal| ≤ 1 / 1000 := by
  subst hJ
  obtain ⟨hf, he⟩ := eval_const (Jt := 0.0) (At := 0.0) (Vt := 0.0) (Pt := 0.0) fτ fJ fA fV fP hτ0
    (by norm_num; linarith) (by linarith) (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith)
  refine ⟨hf, ?_⟩
  exact const_core (n' := ⟨A0.toReal, V0.toReal, P0.toReal⟩) hτ0 hJ6 he hp hv ha hj ep ev ea

variable {S : SCurve.State} {J tj t2 t4 t15 : ℝ}

theorem prod_le {a b A B : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hA : a ≤ A) (hB : b ≤ B) : a * b ≤ A * B :=
  mul_le_mul hA hB hb (ha.trans hA)

set_option maxHeartbeats 4000000 in
/-- A constant-jerk segment `j` of positive duration, at a local time `τ ∈ [0, d + 10⁻⁴]`. -/
theorem mid_const (hT : TableOk S J tj t2 t4 t15) (hP : SC.ProfIn J tj t2 t4 t15) (h15 : t15 ≤ 15)
    (h22 : (SC.node J tj t2 t4 t15 22).p ≤ 4) (ha14 : S.segment[14]!.end_accel = 0.0) {j : ℕ}
    (hj : j < 22) (hd : 0 < (SC.prof J tj t2 t4 t15 j).d)
    (hK : (SC.prof J tj t2 t4 t15 j).kind = .const) {τ : Float32} (fτ : τ.IsFinite)
    (hτ0 : 0 ≤ τ.toReal) (hτ1 : τ.toReal ≤ (SC.prof J tj t2 t4 t15 j).d + 1 / 10 ^ 4) :
    (SCurve.calc_javp_for_segment_const_jerk τ S.segment[j + 1]!.jerk_ref S.segment[j]!.end_accel
      S.segment[j]!.end_vel S.segment[j]!.end_pos 0.0 0.0 0.0 0.0).2.2.2.IsFinite ∧
    |(SCurve.calc_javp_for_segment_const_jerk τ S.segment[j + 1]!.jerk_ref S.segment[j]!.end_accel
      S.segment[j]!.end_vel S.segment[j]!.end_pos 0.0 0.0 0.0 0.0).2.2.2.toReal -
      SC.Seg.pos ⟨.const, (SC.prof J tj t2 t4 t15 j).J, (SC.prof J tj t2 t4 t15 j).d⟩
        (SC.node J tj t2 t4 t15 j) τ.toReal| ≤ 1 / 1000 := by
  obtain ⟨-, hJ⟩ := hT.kind j hj hd
  obtain ⟨-, fA, fV, fP, -⟩ := hT.fin j (by omega)
  obtain ⟨-, -, -, -, fJ⟩ := hT.fin (j + 1) (by omega)
  have ea := hT.acc j (by omega)
  have ev := hT.vel j (by omega)
  have ep : |S.segment[j]!.end_pos.toReal - (SC.node J tj t2 t4 t15 j).p| ≤ 4 / 10 ^ 4 := by
    have := hT.pos j (by omega); split_ifs at this <;> linarith
  obtain ⟨na, nv0, nv1⟩ := SC.node_bounds hP (k := j) (by omega)
  obtain ⟨np0, np1⟩ := node_p hP hj hd
  obtain ⟨hd15, -, hd3, hJd, hJ14⟩ := prof_facts hP h15 hj
  have hJ6 := SC.prof_J hP hj
  have h14 : j = 14 → S.segment[j]!.end_accel.toReal = 0 ∧ (SC.node J tj t2 t4 t15 j).a = 0 := by
    rintro rfl
    exact ⟨by rw [ha14, f32_toReal_0p0],
      (SC.node_a (Jm := J) (tj := tj) (t2 := t2) (t4 := t4) (t15 := t15)).2.2.2.2.2.2.2.1⟩
  generalize S.segment[j]!.end_accel = A0 at *
  generalize S.segment[j]!.end_vel = V0 at *
  generalize S.segment[j]!.end_pos = P0 at *
  generalize (SC.node J tj t2 t4 t15 j) = n at *
  generalize hτr : τ.toReal = x at *
  have bA := abs_le.1 ea
  have bV := abs_le.1 ev
  have bP := abs_le.1 ep
  have bna := abs_le.1 na
  have hP0 : |P0.toReal| ≤ 5 := abs_le.2 ⟨by linarith, by linarith⟩
  have hV0 : |V0.toReal| ≤ 3 + 3 / 10 ^ 5 := abs_le.2 ⟨by linarith, by linarith⟩
  have hA0 : |A0.toReal| ≤ 2 + 1 / 10 ^ 5 := abs_le.2 ⟨by linarith, by linarith⟩
  have aV := abs_nonneg V0.toReal
  have aA := abs_nonneg A0.toReal
  have aJ := abs_nonneg (SC.prof J tj t2 t4 t15 j).J
  have aeV := abs_nonneg (V0.toReal - n.v)
  have aeA := abs_nonneg (A0.toReal - n.a)
  have hx2 := sq_nonneg x
  have hx3 : 0 ≤ x ^ 3 := pow_nonneg hτ0 3
  rcases eq_or_ne j 14 with rfl | h14'
  · -- the constant-velocity segment: `A₀ = 0`, `J = 0`
    obtain ⟨hA, hna⟩ := h14 rfl
    have hJ0 := hJ14 rfl
    have hx : x ≤ 15 + 1 / 10 ^ 4 := by linarith
    have hAx : |A0.toReal| * x ^ 2 = 0 := by rw [hA, abs_zero, zero_mul]
    have hAe : |A0.toReal - n.a| * x ^ 2 = 0 := by rw [hA, hna, sub_zero, abs_zero, zero_mul]
    have hJx : |(SC.prof J tj t2 t4 t15 14).J| * x ^ 3 = 0 := by rw [hJ0, abs_zero, zero_mul]
    rw [← hτr]
    exact const_float fτ fJ fA fV fP (by rw [hτr]; exact hτ0) (by rw [hτr]; linarith) hJ hJ6
      (by linarith) hP0
      (by rw [hτr]; nlinarith [prod_le aV hτ0 hV0 hx]) (by rw [hτr, hAx]; norm_num)
      (by rw [hτr, hJx]; norm_num) ep
      (by rw [hτr]; nlinarith [prod_le aeV hτ0 ev hx]) (by rw [hτr, hAe]; norm_num)
  · have hx : x ≤ 3 + 1 / 10 ^ 4 := by linarith [hd3 h14']
    have hx2' : x ^ 2 ≤ (3 + 1 / 10 ^ 4) ^ 2 := pow_le_pow_left₀ hτ0 hx 2
    have hJx : |(SC.prof J tj t2 t4 t15 j).J| * x ^ 3 ≤ 1 := by
      rcases hJd hK with h0 | h0
      · rw [h0, abs_zero, zero_mul]; norm_num
      · have hx' : x ≤ 1 / 2 + 1 / 10 ^ 4 := by linarith
        have : x ^ 3 ≤ (1 / 2 + 1 / 10 ^ 4) ^ 3 := pow_le_pow_left₀ hτ0 hx' 3
        nlinarith [prod_le aJ hx3 hJ6 this]
    rw [← hτr]
    exact const_float fτ fJ fA fV fP (by rw [hτr]; exact hτ0) (by rw [hτr]; linarith) hJ hJ6
      (by linarith) hP0
      (by rw [hτr]; nlinarith [prod_le aV hτ0 hV0 hx]) (by rw [hτr]; nlinarith [prod_le aA hx2 hA0 hx2'])
      (by rw [hτr]; exact hJx) ep
      (by rw [hτr]; nlinarith [prod_le aeV hτ0 ev hx]) (by rw [hτr]; nlinarith [prod_le aeA hx2 ea hx2'])

/-- A ramp `j` (kind `k`), from the `float` evaluation (`eval_incr`, `eval_decr`) of the code value
`Q` at the start entry `j` with the `float` duration `tjF`. -/
theorem mid_ramp (hT : TableOk S J tj t2 t4 t15) (hP : SC.ProfIn J tj t2 t4 t15) (h15 : t15 ≤ 15)
    (h22 : (SC.node J tj t2 t4 t15 22).p ≤ 4) {j : ℕ} (hj : j < 22)
    (hd : 0 < (SC.prof J tj t2 t4 t15 j).d) {k : SC.Kind}
    (hK : (SC.prof J tj t2 t4 t15 j).kind = k) (hk : k ≠ .const) {τ tjF Q : Float32}
    (htj : |tjF.toReal - tj| ≤ 1 / 10 ^ 5) (hτ0 : 0 ≤ τ.toReal) (hτ2' : τ.toReal ≤ 2 * tj)
    (heval : 1 / 512 ≤ tjF.toReal → tjF.toReal ≤ 1 / 2 → |S.segment[j + 1]!.jerk_ref.toReal| ≤ 8 →
      |S.segment[j]!.end_accel.toReal| ≤ 8 → |S.segment[j]!.end_vel.toReal| ≤ 8 →
      |S.segment[j]!.end_pos.toReal| ≤ 8 →
      Q.IsFinite ∧ |Q.toReal - SC.Seg.pos ⟨k, S.segment[j + 1]!.jerk_ref.toReal, tjF.toReal⟩
        ⟨S.segment[j]!.end_accel.toReal, S.segment[j]!.end_vel.toReal, S.segment[j]!.end_pos.toReal⟩
        τ.toReal| ≤ 1 / 10 ^ 4) :
    Q.IsFinite ∧ |Q.toReal - SC.Seg.pos ⟨k, (SC.prof J tj t2 t4 t15 j).J, (SC.prof J tj t2 t4 t15 j).d⟩
        (SC.node J tj t2 t4 t15 j) τ.toReal| ≤ 1 / 1000 := by
  obtain ⟨-, hJ⟩ := hT.kind j hj hd
  have ea := hT.acc j (by omega)
  have ev := hT.vel j (by omega)
  have ep : |S.segment[j]!.end_pos.toReal - (SC.node J tj t2 t4 t15 j).p| ≤ 4 / 10 ^ 4 := by
    have := hT.pos j (by omega); split_ifs at this <;> linarith
  obtain ⟨na, nv0, nv1⟩ := SC.node_bounds hP (k := j) (by omega)
  obtain ⟨np0, np1⟩ := node_p hP hj hd
  obtain ⟨-, hdtj, -, -, -⟩ := prof_facts hP h15 hj
  have hdt := hdtj (by rw [hK]; exact hk)
  have hJ6 := SC.prof_J hP hj
  have := hP.tj0; have := hP.tj1
  have bA := abs_le.1 ea
  have bV := abs_le.1 ev
  have bP := abs_le.1 ep
  have bna := abs_le.1 na
  have bt := abs_le.1 htj
  obtain ⟨hf, he⟩ := heval (by linarith) (by linarith) (by rw [hJ]; linarith)
    (abs_le.2 ⟨by linarith, by linarith⟩) (abs_le.2 ⟨by linarith, by linarith⟩)
    (abs_le.2 ⟨by linarith, by linarith⟩)
  rw [hJ] at he
  refine ⟨hf, ?_⟩
  rw [hdt]
  exact ramp_core hk hτ0 hτ2' hP.tj0 hP.tj1 htj hJ6 he ep ev ea

set_option maxHeartbeats 4000000 in
/-- **Time in segment `j + 1`** (`T_j ≤ t < T_{j+1}`). -/
theorem case_mid (hL : LibmSpec) (hT : TableOk S J tj t2 t4 t15) (hP : SC.ProfIn J tj t2 t4 t15)
    (h15 : t15 ≤ 15) (h22 : (SC.node J tj t2 t4 t15 22).p ≤ 4)
    (ha14 : S.segment[14]!.end_accel = 0.0) {j : ℕ} (hj : j < 22) {t : Float32} (ft : t.IsFinite)
    (ht1 : t.toReal ≤ 1000) (hle : S.segment[j]!.end_time.toReal ≤ t.toReal)
    (hlt : t.toReal < S.segment[j + 1]!.end_time.toReal) :
    (postP S t (j + 1)).IsFinite ∧
      |(postP S t (j + 1)).toReal - SC.profPos J tj t2 t4 t15 t.toReal| ≤ 3 / 2000 := by
  have hd : 0 < (SC.prof J tj t2 t4 t15 j).d := by
    rcases (SC.prof_d_nonneg hP j).lt_or_eq with h | h
    · exact h
    · have := hT.zero j hj h.symm
      rw [this] at hlt; linarith
  obtain ⟨hty, -⟩ := hT.kind j hj hd
  obtain ⟨fT0, fA, fV, fP, -⟩ := hT.fin j (by omega)
  obtain ⟨fT1, -, -, -, fJ⟩ := hT.fin (j + 1) (by omega)
  have hTj := hT.time j (by omega)
  have hTk := hT.time (j + 1) (by omega)
  have hte := SC.tEnd_nonneg hP j
  have hd15 := (prof_facts hP h15 hj).1
  have hte1 : SC.tEnd J tj t2 t4 t15 (j + 1) =
      SC.tEnd J tj t2 t4 t15 j + (SC.prof J tj t2 t4 t15 j).d := rfl
  have bTj := abs_le.1 hTj
  have bTk := abs_le.1 hTk
  obtain ⟨fτ, eτ⟩ := sub_fl ft fT0 hle (by linarith)
  have bτ := abs_le.1 eτ
  have hτ0 : 0 ≤ (t - S.segment[j]!.end_time).toReal := by linarith
  have hτ1 : (t - S.segment[j]!.end_time).toReal ≤ (SC.prof J tj t2 t4 t15 j).d + 1 / 10 ^ 4 := by
    linarith
  suffices key : (postP S t (j + 1)).IsFinite ∧ |(postP S t (j + 1)).toReal -
      (SC.prof J tj t2 t4 t15 j).pos (SC.node J tj t2 t4 t15 j)
        (t - S.segment[j]!.end_time).toReal| ≤ 1 / 1000 by
    obtain ⟨hf, hQ⟩ := key
    refine ⟨hf, ?_⟩
    have := chain hP h15 hj hTj hTk hle hlt eτ hQ
    linarith
  unfold postP
  simp only [show j + 1 ≠ 0 by omega, show j + 1 ≠ 23 by omega, ↓reduceIte, Nat.add_sub_cancel]
  rw [hty]
  cases hK : (SC.prof J tj t2 t4 t15 j).kind with
  | const =>
    simp only [kindType]
    rw [seg_eta hK]
    exact mid_const hT hP h15 h22 ha14 hj hd hK fτ hτ0 hτ1
  | incr =>
    simp only [kindType]
    rw [seg_eta hK]
    have htj := hT.dur j hj (by rw [hK]; nofun)
    obtain ⟨ftj, etj⟩ := sub_fl fT1 fT0 (by linarith) (by linarith)
    have btj := abs_le.1 etj
    have bt := abs_le.1 htj
    have := hP.tj0
    exact mid_ramp hT hP h15 h22 hj hd hK (by nofun) htj hτ0 (by linarith)
      (fun a b c d e f => eval_incr hL fτ ftj fJ fA fV fP a b hτ0 (by linarith) c d e f)
  | decr =>
    simp only [kindType]
    rw [seg_eta hK]
    have htj := hT.dur j hj (by rw [hK]; nofun)
    obtain ⟨ftj, etj⟩ := sub_fl fT1 fT0 (by linarith) (by linarith)
    have btj := abs_le.1 etj
    have bt := abs_le.1 htj
    have := hP.tj0
    exact mid_ramp hT hP h15 h22 hj hd hK (by nofun) htj hτ0 (by linarith)
      (fun a b c d e f => eval_decr hL fτ ftj fJ fA fV fP a b hτ0 (by linarith) c d e f)

theorem node22_nonneg (hP : SC.ProfIn J tj t2 t4 t15) : 0 ≤ (SC.node J tj t2 t4 t15 22).p := by
  rw [← SC.profPos_of_ge hP le_rfl, ← SC.profPos_of_le hP (le_refl 0)]
  exact SC.profPos_mono hP (SC.tEnd_nonneg hP 22)

set_option maxHeartbeats 4000000 in
/-- **Time after the last end time**: the end node. -/
theorem case_last (hT : TableOk S J tj t2 t4 t15) (hP : SC.ProfIn J tj t2 t4 t15)
    (h22 : (SC.node J tj t2 t4 t15 22).p ≤ 4) {t : Float32} (ft : t.IsFinite)
    (ht1 : t.toReal ≤ 1000) (hge : S.segment[22]!.end_time.toReal ≤ t.toReal) :
    (postP S t 23).IsFinite ∧
      |(postP S t 23).toReal - SC.profPos J tj t2 t4 t15 t.toReal| ≤ 3 / 2000 := by
  unfold postP
  simp only [show (23 : ℕ) ≠ 0 by omega, ↓reduceIte]
  rw [hT.last.1, hT.last.2]
  obtain ⟨fT, -, -, fP, -⟩ := hT.fin 22 (by omega)
  have hTe := abs_le.1 (hT.time 22 le_rfl)
  have hPe : |S.segment[22]!.end_pos.toReal - (SC.node J tj t2 t4 t15 22).p| ≤ 4 / 10 ^ 4 := by
    have := hT.pos 22 le_rfl; simpa using this
  have hn0 := node22_nonneg hP
  have hte := SC.tEnd_nonneg hP 22
  obtain ⟨fτ, eτ⟩ := sub_fl ft fT hge (by linarith)
  have bτ := abs_le.1 eτ
  have bP := abs_le.1 hPe
  have h0 := f32_toReal_0p0
  obtain ⟨hf, he⟩ := eval_const (Jt := 0.0) (At := 0.0) (Vt := 0.0) (Pt := 0.0) fτ
    f32_isFinite_0p0 f32_isFinite_0p0 f32_isFinite_0p0 fP (by linarith) (by linarith)
    (by rw [h0, abs_zero, zero_mul]; norm_num) (by rw [h0, abs_zero, zero_mul]; norm_num)
    (by rw [h0, abs_zero, zero_mul]; norm_num) (abs_le.2 ⟨by linarith, by linarith⟩)
    (by rw [h0, abs_zero]; norm_num) (by rw [h0, abs_zero]; norm_num)
  refine ⟨hf, ?_⟩
  rw [h0] at he
  simp only [SC.cP, abs_zero, zero_mul, add_zero, zero_div] at he
  have hPa : |S.segment[22]!.end_pos.toReal| ≤ 5 := abs_le.2 ⟨by linarith, by linarith⟩
  have hprof : |SC.profPos J tj t2 t4 t15 t.toReal - (SC.node J tj t2 t4 t15 22).p| ≤ 6 / 10 ^ 5 := by
    rcases le_total (SC.tEnd J tj t2 t4 t15 22) t.toReal with h | h
    · rw [SC.profPos_of_ge hP h, sub_self, abs_zero]; norm_num
    · have := SC.profPos_lip hP t.toReal (SC.tEnd J tj t2 t4 t15 22)
      rw [SC.profPos_of_ge hP le_rfl,
        abs_of_nonpos (by linarith : t.toReal - SC.tEnd J tj t2 t4 t15 22 ≤ 0)] at this
      linarith
  have q1 := abs_le.1 he
  have q2 := abs_le.1 hprof
  refine abs_le.2 ⟨by linarith, by linarith⟩

set_option maxHeartbeats 4000000 in
/-- **Time before the first end time** (`t ≥ 0`, so within `2·10⁻⁵` of `0`). -/
theorem case_zero (hT : TableOk S J tj t2 t4 t15) (hP : SC.ProfIn J tj t2 t4 t15) {t : Float32}
    (ft : t.IsFinite) (ht0 : 0 ≤ t.toReal) (hlt : t.toReal < S.segment[0]!.end_time.toReal) :
    (postP S t 0).IsFinite ∧
      |(postP S t 0).toReal - SC.profPos J tj t2 t4 t15 t.toReal| ≤ 3 / 2000 := by
  unfold postP
  simp only [↓reduceIte]
  obtain ⟨fT, fA, fV, fP, -⟩ := hT.fin 0 (by omega)
  have hTe := abs_le.1 (hT.time 0 (by omega))
  have hAe := abs_le.1 (hT.acc 0 (by omega))
  have hVe := abs_le.1 (hT.vel 0 (by omega))
  have hPe : |S.segment[0]!.end_pos.toReal - (SC.node J tj t2 t4 t15 0).p| ≤ 4 / 10 ^ 5 := by
    have := hT.pos 0 (by omega); simpa using this
  have bP := abs_le.1 hPe
  have e0 : SC.tEnd J tj t2 t4 t15 0 = 0 := rfl
  have n0 : SC.node J tj t2 t4 t15 0 = ⟨0, 0, 0⟩ := rfl
  rw [e0] at hTe
  rw [n0] at hAe hVe bP
  dsimp only at hAe hVe bP
  have hm := sce_max
  obtain ⟨fτ, eτ⟩ := Float32.sub_err_all ft fT (by rw [abs_le]; constructor <;> linarith)
  rw [show (2 : ℝ) ^ (-24 : ℤ) = 1 / 16777216 by norm_num,
    abs_of_neg (by linarith : t.toReal - S.segment[0]!.end_time.toReal < 0)] at eτ
  have bτ := abs_le.1 eτ
  generalize (t - S.segment[0]!.end_time) = τ at *
  have hw : |τ.toReal| ≤ 3 / 10 ^ 5 := abs_le.2 ⟨by linarith, by linarith⟩
  have hw0 := abs_nonneg τ.toReal
  have hA : |S.segment[0]!.end_accel.toReal| ≤ 1 / 10 ^ 5 := abs_le.2 ⟨by linarith, by linarith⟩
  have hV : |S.segment[0]!.end_vel.toReal| ≤ 3 / 10 ^ 5 := abs_le.2 ⟨by linarith, by linarith⟩
  have hP0 : |S.segment[0]!.end_pos.toReal| ≤ 4 / 10 ^ 5 := abs_le.2 ⟨by linarith, by linarith⟩
  have aA := abs_nonneg S.segment[0]!.end_accel.toReal
  have aV := abs_nonneg S.segment[0]!.end_vel.toReal
  have hw2 : |τ.toReal| ^ 2 ≤ (3 / 10 ^ 5) ^ 2 := pow_le_pow_left₀ hw0 hw 2
  have hVw := prod_le aV hw0 hV hw
  have hAw := prod_le aA (sq_nonneg _) hA hw2
  have h0 := f32_toReal_0p0
  obtain ⟨hf, he⟩ := eval_const_abs (Jt := 0.0) (At := 0.0) (Vt := 0.0) (Pt := 0.0) fτ
    f32_isFinite_0p0 fA fV fP (by linarith) (by rw [h0, abs_zero, zero_mul]; norm_num)
    (by linarith) (by linarith) (by linarith) (by rw [h0, abs_zero]; norm_num) (by linarith)
  refine ⟨hf, ?_⟩
  rw [h0, abs_zero, zero_mul, add_zero] at he
  have hc : |SC.cP ⟨S.segment[0]!.end_accel.toReal, S.segment[0]!.end_vel.toReal,
      S.segment[0]!.end_pos.toReal⟩ 0 τ.toReal| ≤ 5 / 10 ^ 5 := by
    simp only [SC.cP, zero_mul, zero_div, add_zero]
    have a1 := abs_add_le (S.segment[0]!.end_pos.toReal + S.segment[0]!.end_vel.toReal * τ.toReal)
      (S.segment[0]!.end_accel.toReal * τ.toReal ^ 2 / 2)
    have a2 := abs_add_le S.segment[0]!.end_pos.toReal (S.segment[0]!.end_vel.toReal * τ.toReal)
    have a3 : |S.segment[0]!.end_vel.toReal * τ.toReal| = |S.segment[0]!.end_vel.toReal| * |τ.toReal| :=
      abs_mul _ _
    have a4 : |S.segment[0]!.end_accel.toReal * τ.toReal ^ 2 / 2| =
        |S.segment[0]!.end_accel.toReal| * |τ.toReal| ^ 2 / 2 := by
      rw [abs_div, abs_mul, abs_pow, abs_two]
    linarith
  have hprof : |SC.profPos J tj t2 t4 t15 t.toReal| ≤ 6 / 10 ^ 5 := by
    have := SC.profPos_lip hP t.toReal 0
    rw [SC.profPos_of_le hP (le_refl 0), sub_zero, sub_zero, abs_of_nonneg ht0] at this
    linarith
  have q1 := abs_le.1 he
  have q2 := abs_le.1 hc
  have q3 := abs_le.1 hprof
  refine abs_le.2 ⟨by linarith, by linarith⟩

end SCG

end

end Contracts.Mission
