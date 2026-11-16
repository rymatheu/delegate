import Contracts.Mission.SCurveCalc
import Contracts.Mission.SCurveProfile
import Contracts.Mission.SCurveTableFinal

/-!
# The segment table of `SCurve::add_segments` in `float`

From a freshly initialized S-curve (`SCurve::init`: one segment, the start node at rest at time `0`)
and the output of `calculate_path` on the half leg (`CPOk`), `add_segments` writes segments `1 … 22`.
`add_segments_spec`: the table approximates the real profile `SC.prof`/`SC.node`/`SC.tEnd` with the
durations the code gives the segments (`eff` gates `t₂`, `t₄`, `t₁₅` by `is_positive`): every end
time, acceleration, velocity and position within a small absolute error, the segment types and
jerks as in `SC.prof`, ramps with `float` durations within `10⁻⁵` of `t_j`, zero-duration
segments with equal end times, and the last node at rest exactly.

Segment `0` is never written by `add_segments`, so its `jerk_ref` is finite only if it was
(`hj0`; `SCurve::init` writes `0`). The proof: the code writes the table `SCT.tbl`
(`SCurveTableCode.lean`); each entry is near the next real node (`SCurveTableFloat.lean`,
`SCurveTableNear.lean`, chains in `SCurveTableChain.lean`, with a second regime for legs below
`0.03` for the end bound); `t₁₅` in `SCurveTableT15.lean`.
-/

namespace Contracts.Mission

open Float.Model UnpackedFloat AC_WPNav_lib

noncomputable section

/-- The code's segment type of a real segment kind. -/
def kindType : SC.Kind → SCurve.SegmentType
  | .const => .CONSTANT_JERK
  | .incr => .POSITIVE_JERK
  | .decr => .NEGATIVE_JERK

/-- **The table approximates the profile** `(J, t_j, t₂, t₄, t₁₅)`. -/
structure TableOk (s : SCurve.State) (J tj t2 t4 t15 : ℝ) : Prop where
  num : s.num_segs = 23
  size : s.segment.size = 23
  fin : ∀ k < 23, s.segment[k]!.end_time.IsFinite ∧ s.segment[k]!.end_accel.IsFinite ∧
    s.segment[k]!.end_vel.IsFinite ∧ s.segment[k]!.end_pos.IsFinite ∧ s.segment[k]!.jerk_ref.IsFinite
  time : ∀ k ≤ 22, |s.segment[k]!.end_time.toReal - SC.tEnd J tj t2 t4 t15 k| ≤ 2 / 10 ^ 5
  acc : ∀ k ≤ 22, |s.segment[k]!.end_accel.toReal - (SC.node J tj t2 t4 t15 k).a| ≤ 1 / 10 ^ 5
  vel : ∀ k ≤ 22, |s.segment[k]!.end_vel.toReal - (SC.node J tj t2 t4 t15 k).v| ≤ 3 / 10 ^ 5
  pos : ∀ k ≤ 22, |s.segment[k]!.end_pos.toReal - (SC.node J tj t2 t4 t15 k).p| ≤
    if k ≤ 14 then 4 / 10 ^ 5 else 4 / 10 ^ 4
  /-- Times are nondecreasing. -/
  mono : ∀ k < 22, s.segment[k]!.end_time.toReal ≤ s.segment[k + 1]!.end_time.toReal
  /-- Segments of positive duration: the type and jerk of `SC.prof`. -/
  kind : ∀ k < 22, 0 < (SC.prof J tj t2 t4 t15 k).d →
    s.segment[k + 1]!.seg_type = kindType (SC.prof J tj t2 t4 t15 k).kind ∧
      s.segment[k + 1]!.jerk_ref.toReal = (SC.prof J tj t2 t4 t15 k).J
  /-- Segments of zero duration end when the previous one ends. -/
  zero : ∀ k < 22, (SC.prof J tj t2 t4 t15 k).d = 0 →
    s.segment[k + 1]!.end_time = s.segment[k]!.end_time
  /-- The ramps' `float` durations, as `get_jerk_accel_vel_pos_at_time` recomputes them. -/
  dur : ∀ k < 22, (SC.prof J tj t2 t4 t15 k).kind ≠ .const →
    |(s.segment[k + 1]!.end_time - s.segment[k]!.end_time).toReal - tj| ≤ 1 / 10 ^ 5
  /-- The last node is at rest. -/
  last : s.segment[22]!.end_accel = 0.0 ∧ s.segment[22]!.end_vel = 0.0

namespace SCT

theorem props_incr {e : SCurve.segment_t} {tj JF : Float32} {J : ℝ}
    (hpos : is_positive_float tj = true) (fT : e.end_time.IsFinite) (hT : |e.end_time.toReal| ≤ 26)
    (ft : tj.IsFinite) (ht0 : 0 ≤ tj.toReal) (ht1 : tj.toReal ≤ 1 / 4) (hJ : JF.toReal = J) :
    e.end_time.toReal ≤ (incrE e tj JF).end_time.toReal ∧
    (tj.toReal = 0 → (incrE e tj JF).end_time = e.end_time) ∧
    (0 < tj.toReal → (incrE e tj JF).seg_type = kindType .incr ∧ (incrE e tj JF).jerk_ref.toReal = J) ∧
    |((incrE e tj JF).end_time - e.end_time).toReal - tj.toReal| ≤ 1 / 10 ^ 5 := by
  obtain ⟨e1, -, -, -, e5, e6⟩ := incrE_pos (p := e) (Jm := JF) hpos
  have hlo := (eff_pos ft hpos).2
  rw [e1, e5, e6]
  refine ⟨time_mono fT ft (by linarith) ht0 (by linarith), fun h => by linarith,
    fun _ => ⟨rfl, hJ⟩, ?_⟩
  have := (time_dur fT ft hT ht0 ht1).2
  linarith

theorem props_decr {e : SCurve.segment_t} {tj JF : Float32} {J : ℝ}
    (hpos : is_positive_float tj = true) (fT : e.end_time.IsFinite) (hT : |e.end_time.toReal| ≤ 26)
    (ft : tj.IsFinite) (ht0 : 0 ≤ tj.toReal) (ht1 : tj.toReal ≤ 1 / 4) (hJ : JF.toReal = J) :
    e.end_time.toReal ≤ (decrE e tj JF).end_time.toReal ∧
    (tj.toReal = 0 → (decrE e tj JF).end_time = e.end_time) ∧
    (0 < tj.toReal → (decrE e tj JF).seg_type = kindType .decr ∧ (decrE e tj JF).jerk_ref.toReal = J) ∧
    |((decrE e tj JF).end_time - e.end_time).toReal - tj.toReal| ≤ 1 / 10 ^ 5 := by
  obtain ⟨e1, -, -, -, e5, e6⟩ := decrE_pos (p := e) (Jm := JF) hpos
  have hlo := (eff_pos ft hpos).2
  rw [e1, e5, e6]
  refine ⟨time_mono fT ft (by linarith) ht0 (by linarith), fun h => by linarith,
    fun _ => ⟨rfl, hJ⟩, ?_⟩
  have := (time_dur fT ft hT ht0 ht1).2
  linarith

theorem props_const {e : SCurve.segment_t} {tin J0 : Float32} {J : ℝ}
    (fT : e.end_time.IsFinite) (hT : |e.end_time.toReal| ≤ 26) (ft : tin.IsFinite)
    (ht1 : is_positive_float tin = true → tin.toReal ≤ 15) (hJ : J0.toReal = J) :
    e.end_time.toReal ≤ (constE e tin J0).end_time.toReal ∧
    (eff tin.toReal = 0 → (constE e tin J0).end_time = e.end_time) ∧
    (0 < eff tin.toReal → (constE e tin J0).seg_type = kindType .const ∧
      (constE e tin J0).jerk_ref.toReal = J) := by
  rcases Bool.eq_false_or_eq_true (is_positive_float tin) with hp | hp
  · obtain ⟨e1, -, -, -, e5, e6⟩ := constE_pos (p := e) (J0 := J0) hp
    obtain ⟨he, hlo⟩ := eff_pos ft hp
    rw [e1, e5, e6, he]
    have h2 : (0 : ℝ) < 1 / 2 ^ 23 := by norm_num
    refine ⟨time_mono fT ft (by linarith) (by linarith) (by linarith [ht1 hp]), fun h => by linarith,
      fun _ => ⟨rfl, hJ⟩⟩
  · obtain ⟨e1, -, -, -, e5, e6⟩ := constE_neg (p := e) (J0 := J0) hp
    obtain ⟨he, -⟩ := eff_neg ft hp
    rw [e1, e5, e6, he]
    exact ⟨le_rfl, fun _ => rfl, fun h => absurd h (lt_irrefl 0)⟩

theorem step_props {L Jm tj t2 t4 : Float32} {t15 : ℝ} {e : SCurve.segment_t} {k : ℕ} (hk : k < 22)
    (fJ : Jm.IsFinite) (ft : tj.IsFinite) (ft2 : t2.IsFinite) (ft4 : t4.IsFinite)
    (htj0 : 1 / 300 ≤ tj.toReal) (htj1 : tj.toReal ≤ 1 / 4) (ht21 : t2.toReal ≤ 1 / 2)
    (ht41 : t4.toReal ≤ 3)
    (h15 : k = 14 → t15 = eff (t15F L e).toReal ∧ (t15F L e).IsFinite ∧
      (is_positive_float (t15F L e) = true → (t15F L e).toReal ≤ 15))
    (fT : e.end_time.IsFinite) (hT : |e.end_time.toReal| ≤ 26) :
    e.end_time.toReal ≤ (stepE L Jm tj t2 t4 t2 k e).end_time.toReal ∧
    ((SC.prof Jm.toReal tj.toReal (eff t2.toReal) (eff t4.toReal) t15 k).d = 0 →
      (stepE L Jm tj t2 t4 t2 k e).end_time = e.end_time) ∧
    (0 < (SC.prof Jm.toReal tj.toReal (eff t2.toReal) (eff t4.toReal) t15 k).d →
      (stepE L Jm tj t2 t4 t2 k e).seg_type =
        kindType (SC.prof Jm.toReal tj.toReal (eff t2.toReal) (eff t4.toReal) t15 k).kind ∧
      (stepE L Jm tj t2 t4 t2 k e).jerk_ref.toReal =
        (SC.prof Jm.toReal tj.toReal (eff t2.toReal) (eff t4.toReal) t15 k).J) ∧
    ((SC.prof Jm.toReal tj.toReal (eff t2.toReal) (eff t4.toReal) t15 k).kind ≠ .const →
      |((stepE L Jm tj t2 t4 t2 k e).end_time - e.end_time).toReal - tj.toReal| ≤ 1 / 10 ^ 5) ∧
    (stepE L Jm tj t2 t4 t2 k e).jerk_ref.IsFinite := by
  have hpos : is_positive_float tj = true := sce_isPos ft (by linarith)
  have fJn : (-Jm).IsFinite := (Float32.isFinite_neg _).2 fJ
  interval_cases k <;> simp only [SC.prof, stepE]
  · -- k = 0
    have h := props_incr (e := e) (JF := Jm) (J := Jm.toReal) hpos fT hT ft (by linarith) htj1 rfl
    exact ⟨h.1, h.2.1, h.2.2.1, fun _ => h.2.2.2, incrE_jerk_fin fJ⟩
  · -- k = 1
    have h := props_const (e := e) (tin := t2) (J0 := Jm) (J := Jm.toReal) fT hT ft2 (fun _ => by linarith) rfl
    exact ⟨h.1, h.2.1, h.2.2, fun h => absurd rfl h, by rw [constE_jerk]; exact fJ⟩
  · -- k = 2
    have h := props_decr (e := e) (JF := Jm) (J := Jm.toReal) hpos fT hT ft (by linarith) htj1 rfl
    exact ⟨h.1, h.2.1, h.2.2.1, fun _ => h.2.2.2, decrE_jerk_fin fJ⟩
  · -- k = 3
    have h := props_const (e := e) (tin := t4) (J0 := (0.0 : Float32)) (J := 0) fT hT ft4 (fun _ => by linarith) f32_toReal_0p0
    exact ⟨h.1, h.2.1, h.2.2, fun h => absurd rfl h, by rw [constE_jerk]; exact f32_isFinite_0p0⟩
  · -- k = 4
    have h := props_incr (e := e) (JF := -Jm) (J := -Jm.toReal) hpos fT hT ft (by linarith) htj1 (Float32.toReal_neg _)
    exact ⟨h.1, h.2.1, h.2.2.1, fun _ => h.2.2.2, incrE_jerk_fin fJn⟩
  · -- k = 5
    have h := props_const (e := e) (tin := t2) (J0 := -Jm) (J := -Jm.toReal) fT hT ft2 (fun _ => by linarith) (Float32.toReal_neg _)
    exact ⟨h.1, h.2.1, h.2.2, fun h => absurd rfl h, by rw [constE_jerk]; exact fJn⟩
  · -- k = 6
    have h := props_decr (e := e) (JF := -Jm) (J := -Jm.toReal) hpos fT hT ft (by linarith) htj1 (Float32.toReal_neg _)
    exact ⟨h.1, h.2.1, h.2.2.1, fun _ => h.2.2.2, decrE_jerk_fin fJn⟩
  · -- k = 7
    obtain ⟨e1, -, -, -, -, e6⟩ := constE_neg (p := e) (tin := 0.0) (J0 := 0.0) isPos_zero
    rw [e1, e6]
    exact ⟨le_rfl, fun _ => rfl, fun h => absurd h (lt_irrefl 0), fun h => absurd rfl h,
      f32_isFinite_0p0⟩
  · -- k = 8
    obtain ⟨e1, -, -, -, -, e6⟩ := constE_neg (p := e) (tin := 0.0) (J0 := 0.0) isPos_zero
    rw [e1, e6]
    exact ⟨le_rfl, fun _ => rfl, fun h => absurd h (lt_irrefl 0), fun h => absurd rfl h,
      f32_isFinite_0p0⟩
  · -- k = 9
    obtain ⟨e1, -, -, -, -, e6⟩ := constE_neg (p := e) (tin := 0.0) (J0 := 0.0) isPos_zero
    rw [e1, e6]
    exact ⟨le_rfl, fun _ => rfl, fun h => absurd h (lt_irrefl 0), fun h => absurd rfl h,
      f32_isFinite_0p0⟩
  · -- k = 10
    obtain ⟨e1, -, -, -, -, e6⟩ := constE_neg (p := e) (tin := 0.0) (J0 := 0.0) isPos_zero
    rw [e1, e6]
    exact ⟨le_rfl, fun _ => rfl, fun h => absurd h (lt_irrefl 0), fun h => absurd rfl h,
      f32_isFinite_0p0⟩
  · -- k = 11
    obtain ⟨e1, -, -, -, -, e6⟩ := constE_neg (p := e) (tin := 0.0) (J0 := 0.0) isPos_zero
    rw [e1, e6]
    exact ⟨le_rfl, fun _ => rfl, fun h => absurd h (lt_irrefl 0), fun h => absurd rfl h,
      f32_isFinite_0p0⟩
  · -- k = 12
    obtain ⟨e1, -, -, -, -, e6⟩ := constE_neg (p := e) (tin := 0.0) (J0 := 0.0) isPos_zero
    rw [e1, e6]
    exact ⟨le_rfl, fun _ => rfl, fun h => absurd h (lt_irrefl 0), fun h => absurd rfl h,
      f32_isFinite_0p0⟩
  · -- k = 13
    obtain ⟨e1, -, -, -, -, e6⟩ := constE_neg (p := e) (tin := 0.0) (J0 := 0.0) isPos_zero
    rw [e1, e6]
    exact ⟨le_rfl, fun _ => rfl, fun h => absurd h (lt_irrefl 0), fun h => absurd rfl h,
      f32_isFinite_0p0⟩
  · -- k = 14
    obtain ⟨he, fq, hq⟩ := h15 rfl
    rw [he]
    have h := props_const (e := e) (tin := t15F L e) (J0 := (0.0 : Float32)) (J := 0) fT hT fq hq f32_toReal_0p0
    exact ⟨h.1, h.2.1, h.2.2, fun h => absurd rfl h, by rw [constE_jerk]; exact f32_isFinite_0p0⟩
  · -- k = 15
    have h := props_incr (e := e) (JF := -Jm) (J := -Jm.toReal) hpos fT hT ft (by linarith) htj1 (Float32.toReal_neg _)
    exact ⟨h.1, h.2.1, h.2.2.1, fun _ => h.2.2.2, incrE_jerk_fin fJn⟩
  · -- k = 16
    have h := props_const (e := e) (tin := t2) (J0 := -Jm) (J := -Jm.toReal) fT hT ft2 (fun _ => by linarith) (Float32.toReal_neg _)
    exact ⟨h.1, h.2.1, h.2.2, fun h => absurd rfl h, by rw [constE_jerk]; exact fJn⟩
  · -- k = 17
    have h := props_decr (e := e) (JF := -Jm) (J := -Jm.toReal) hpos fT hT ft (by linarith) htj1 (Float32.toReal_neg _)
    exact ⟨h.1, h.2.1, h.2.2.1, fun _ => h.2.2.2, decrE_jerk_fin fJn⟩
  · -- k = 18
    have h := props_const (e := e) (tin := t4) (J0 := (0.0 : Float32)) (J := 0) fT hT ft4 (fun _ => by linarith) f32_toReal_0p0
    exact ⟨h.1, h.2.1, h.2.2, fun h => absurd rfl h, by rw [constE_jerk]; exact f32_isFinite_0p0⟩
  · -- k = 19
    have h := props_incr (e := e) (JF := Jm) (J := Jm.toReal) hpos fT hT ft (by linarith) htj1 rfl
    exact ⟨h.1, h.2.1, h.2.2.1, fun _ => h.2.2.2, incrE_jerk_fin fJ⟩
  · -- k = 20
    have h := props_const (e := e) (tin := t2) (J0 := Jm) (J := Jm.toReal) fT hT ft2 (fun _ => by linarith) rfl
    exact ⟨h.1, h.2.1, h.2.2, fun h => absurd rfl h, by rw [constE_jerk]; exact fJ⟩
  · -- k = 21
    have h := props_decr (e := e) (JF := Jm) (J := Jm.toReal) hpos fT hT ft (by linarith) htj1 rfl
    exact ⟨h.1, h.2.1, h.2.2.1, fun _ => h.2.2.2, decrE_jerk_fin fJ⟩

end SCT

/-- **Assembly**: the table `E` written into `S`, near the profile at every node. -/
theorem tableOk_of {S : SCurve.State} {E : ℕ → SCurve.segment_t} {L Jm tj t2 t4 : Float32} {t15 : ℝ}
    (hEs : ∀ k, E (k + 1) = SCT.stepE L Jm tj t2 t4 t2 k (E k))
    (hnum : S.num_segs.toNat = 23) (hArr : SCT.Arr S.segment 23 E) (hj0 : (E 0).jerk_ref.IsFinite)
    (fJ : Jm.IsFinite) (ft : tj.IsFinite) (ft2 : t2.IsFinite) (ft4 : t4.IsFinite)
    (htj0 : 1 / 300 ≤ tj.toReal) (htj1 : tj.toReal ≤ 1 / 4) (ht21 : t2.toReal ≤ 1 / 2)
    (ht41 : t4.toReal ≤ 3)
    (h15 : t15 = eff (SCT.t15F L (E 14)).toReal ∧ (SCT.t15F L (E 14)).IsFinite ∧
      (is_positive_float (SCT.t15F L (E 14)) = true → (SCT.t15F L (E 14)).toReal ≤ 15))
    (htE : ∀ k ≤ 22, 0 ≤ SC.tEnd Jm.toReal tj.toReal (eff t2.toReal) (eff t4.toReal) t15 k ∧
      SC.tEnd Jm.toReal tj.toReal (eff t2.toReal) (eff t4.toReal) t15 k ≤ 25)
    (hNear : ∀ k ≤ 22, SCT.Near (E k) (SC.tEnd Jm.toReal tj.toReal (eff t2.toReal) (eff t4.toReal) t15 k)
      (SC.node Jm.toReal tj.toReal (eff t2.toReal) (eff t4.toReal) t15 k) (2 / 10 ^ 5) (1 / 10 ^ 5)
      (3 / 10 ^ 5) (if k ≤ 14 then 4 / 10 ^ 5 else 4 / 10 ^ 4))
    (hlast : (E 22).end_accel = 0.0 ∧ (E 22).end_vel = 0.0) :
    TableOk S Jm.toReal tj.toReal (eff t2.toReal) (eff t4.toReal) t15 := by
  have hS : ∀ k ≤ 22, S.segment[k]! = E k := fun k hk => hArr.2 k (by omega)
  have hTb : ∀ k ≤ 22, (E k).end_time.IsFinite ∧ |(E k).end_time.toReal| ≤ 26 := fun k hk => by
    refine ⟨(hNear k hk).1.1, ?_⟩
    have h1 := abs_le.1 (hNear k hk).1.2
    have h2 := htE k hk
    rw [abs_le]; constructor <;> linarith
  have hP := fun k (hk : k < 22) => SCT.step_props (e := E k) hk fJ ft ft2 ft4 htj0 htj1 ht21 ht41
    (fun h => by subst h; exact h15) (hTb k (by omega)).1 (hTb k (by omega)).2
  refine ⟨?_, hArr.1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · have : S.num_segs.toNat = (23 : UInt8).toNat := hnum
    exact UInt8.toNat_inj.1 this
  · intro k hk
    rw [hS k (by omega)]
    obtain ⟨a, b, c, d⟩ := (hNear k (by omega)).fin
    refine ⟨a, b, c, d, ?_⟩
    rcases k with _ | k
    · exact hj0
    · rw [hEs]; exact (hP k (by omega)).2.2.2.2
  · intro k hk; rw [hS k hk]; exact (hNear k hk).1.2
  · intro k hk; rw [hS k hk]; exact (hNear k hk).2.1.2
  · intro k hk; rw [hS k hk]; exact (hNear k hk).2.2.1.2
  · intro k hk; rw [hS k hk]; exact (hNear k hk).2.2.2.2
  · intro k hk; rw [hS k (by omega), hS (k + 1) (by omega), hEs]; exact (hP k hk).1
  · intro k hk hd; rw [hS (k + 1) (by omega), hEs]; exact (hP k hk).2.2.1 hd
  · intro k hk hd; rw [hS (k + 1) (by omega), hS k (by omega), hEs]; exact (hP k hk).2.1 hd
  · intro k hk hc; rw [hS (k + 1) (by omega), hS k (by omega), hEs]; exact (hP k hk).2.2.2.1 hc
  · rw [hS 22 le_rfl]; exact hlast


set_option maxHeartbeats 4000000 in
/-- **`add_segments` on the mission's ranges.** -/
theorem add_segments_spec (hL : LibmSpec) {s : SCurve.State} {L : Float32}
    (hsz : s.segment.size = 23) (hn : s.num_segs = 1)
    (h0 : s.segment[0]!.end_time = 0.0 ∧ s.segment[0]!.end_accel = 0.0 ∧
      s.segment[0]!.end_vel = 0.0 ∧ s.segment[0]!.end_pos = 0.0)
    (hj0 : s.segment[0]!.jerk_ref.IsFinite)
    (fL : L.IsFinite) (hL0 : 2 / 10 ^ 4 ≤ L.toReal) (hL1 : L.toReal ≤ 362 / 100)
    (hcp : CPOk (L * 0.5).toReal (SCurve.calculate_path s.snap_max s.jerk_max 0.0 s.accel_max
      s.vel_max (L * 0.5) 0.0 0.0 0.0 0.0 0.0)) :
    ∃ t15 : ℝ, 0 ≤ t15 ∧ t15 ≤ 15 ∧
      SC.ProfIn (SCurve.calculate_path s.snap_max s.jerk_max 0.0 s.accel_max s.vel_max (L * 0.5)
          0.0 0.0 0.0 0.0 0.0).1.toReal
        (SCurve.calculate_path s.snap_max s.jerk_max 0.0 s.accel_max s.vel_max (L * 0.5)
          0.0 0.0 0.0 0.0 0.0).2.1.toReal
        (eff (SCurve.calculate_path s.snap_max s.jerk_max 0.0 s.accel_max s.vel_max (L * 0.5)
          0.0 0.0 0.0 0.0 0.0).2.2.1.toReal)
        (eff (SCurve.calculate_path s.snap_max s.jerk_max 0.0 s.accel_max s.vel_max (L * 0.5)
          0.0 0.0 0.0 0.0 0.0).2.2.2.1.toReal) t15 ∧
      TableOk (SCurve.add_segments s L)
        (SCurve.calculate_path s.snap_max s.jerk_max 0.0 s.accel_max s.vel_max (L * 0.5)
          0.0 0.0 0.0 0.0 0.0).1.toReal
        (SCurve.calculate_path s.snap_max s.jerk_max 0.0 s.accel_max s.vel_max (L * 0.5)
          0.0 0.0 0.0 0.0 0.0).2.1.toReal
        (eff (SCurve.calculate_path s.snap_max s.jerk_max 0.0 s.accel_max s.vel_max (L * 0.5)
          0.0 0.0 0.0 0.0 0.0).2.2.1.toReal)
        (eff (SCurve.calculate_path s.snap_max s.jerk_max 0.0 s.accel_max s.vel_max (L * 0.5)
          0.0 0.0 0.0 0.0 0.0).2.2.2.1.toReal) t15 ∧
      (SC.node (SCurve.calculate_path s.snap_max s.jerk_max 0.0 s.accel_max s.vel_max (L * 0.5)
          0.0 0.0 0.0 0.0 0.0).1.toReal
        (SCurve.calculate_path s.snap_max s.jerk_max 0.0 s.accel_max s.vel_max (L * 0.5)
          0.0 0.0 0.0 0.0 0.0).2.1.toReal
        (eff (SCurve.calculate_path s.snap_max s.jerk_max 0.0 s.accel_max s.vel_max (L * 0.5)
          0.0 0.0 0.0 0.0 0.0).2.2.1.toReal)
        (eff (SCurve.calculate_path s.snap_max s.jerk_max 0.0 s.accel_max s.vel_max (L * 0.5)
          0.0 0.0 0.0 0.0 0.0).2.2.2.1.toReal) t15 22).p ≤ L.toReal * (1 + 1 / 1000) + 1 / 10 ^ 4 := by
  generalize hcpe : SCurve.calculate_path s.snap_max s.jerk_max 0.0 s.accel_max s.vel_max (L * 0.5)
    0.0 0.0 0.0 0.0 0.0 = cp at hcp ⊢
  obtain ⟨Jm, tj, t2, t4, t6⟩ := cp
  have ht6 : t6 = t2 := hcp.t6
  subst t6
  dsimp only at hcp ⊢
  -- the code: the table `E`
  have hz : is_zero_float L = false := by
    rcases Bool.eq_false_or_eq_true (is_zero_float L) with h | h
    · have := (wp_isZero_iff fL).1 h
      have e23 : (2 : ℝ) ^ (-23 : ℤ) = 1 / 2 ^ 23 := by norm_num
      rw [e23, abs_of_pos (by linarith)] at this
      linarith
    · exact h
  obtain ⟨hnum, hArr⟩ := SCT.add_segments_tbl s L hsz hn hz hcpe
  generalize hEdef : SCT.tbl s.segment[0]! L Jm tj t2 t4 t2 = E at hArr
  have hEs : ∀ k, E (k + 1) = SCT.stepE L Jm tj t2 t4 t2 k (E k) := fun k => by rw [← hEdef]; rfl
  have hE0 : E 0 = s.segment[0]! := by rw [← hEdef]; rfl
  have hseg : ∀ k ≤ 22, (SCurve.add_segments s L).segment[k]! = E k := fun k hk => hArr.2 k (by omega)
  generalize SCurve.add_segments s L = S at hnum hArr hseg ⊢
  -- the parameters
  have fJ : Jm.IsFinite := hcp.fJ
  have ft : tj.IsFinite := hcp.ftj
  have ft2 : t2.IsFinite := hcp.ft2
  have ft4 : t4.IsFinite := hcp.ft4
  have hJ0 : 0 < Jm.toReal := hcp.J0
  have hJ1 : Jm.toReal ≤ 6 := hcp.J1
  have htj0 : 1 / 300 ≤ tj.toReal := hcp.tj0
  have htj1 : tj.toReal ≤ 1 / 4 := hcp.tj1
  have ht21 : t2.toReal ≤ 1 / 2 := hcp.t21
  have ht40 : 0 ≤ t4.toReal := hcp.t40
  have ht41 : t4.toReal ≤ 3 := hcp.t41
  have hA : Jm.toReal * (tj.toReal + eff t2.toReal) ≤ 2 := hcp.A
  have hp7 : SC.p7 (Jm.toReal * (tj.toReal + eff t2.toReal)) (2 * tj.toReal + eff t2.toReal)
      (eff t4.toReal) ≤ (L * 0.5).toReal * (1 + 1 / 1000) := hcp.p7
  have hlow : (L * 0.5).toReal * (1 - 1 / 10 ^ 4) ≤ SC.p7 (Jm.toReal * (tj.toReal + eff t2.toReal))
      (2 * tj.toReal + eff t2.toReal) (eff t4.toReal) ∨
      1 / 4 ≤ Jm.toReal * (tj.toReal + eff t2.toReal) *
        (2 * tj.toReal + eff t2.toReal + eff t4.toReal) := hcp.low
  have e20 := eff_nonneg t2.toReal
  have e40 := eff_nonneg t4.toReal
  have e21 : eff t2.toReal ≤ 1 / 2 := by
    rcases eff_cases t2.toReal with h | h <;> rw [h.1] <;> linarith
  have e41 : eff t4.toReal ≤ 3 := by
    rcases eff_cases t4.toReal with h | h <;> rw [h.1] <;> linarith
  -- `L * 0.5`
  have hLh : |(L * 0.5).toReal - L.toReal / 2| ≤ 11 / 10 ^ 8 := by
    have a := A32.mul_c (A32.of_exact fL) (A32.of_exact Float32.isFinite_half) (Ra := 362 / 100)
      (Rb := 1 / 2) (e := 11 / 10 ^ 8) (by rw [abs_of_pos (by linarith)]; linarith)
      (by rw [Float32.toReal_half]; norm_num) le_rfl le_rfl (by norm_num [capF]) (by norm_num)
    have := a.2
    rw [Float32.toReal_half] at this
    rw [show L.toReal / 2 = L.toReal * (1 / 2) by ring]; exact this
  -- the node `7`
  set A := Jm.toReal * (tj.toReal + eff t2.toReal) with hAdef
  set R := 2 * tj.toReal + eff t2.toReal with hRdef
  have n7 := SC.node_7_eq (Jm := Jm.toReal) (tj := tj.toReal) (t2 := eff t2.toReal)
    (t4 := eff t4.toReal) (t15 := 0) (by linarith)
  have hA0 : 0 ≤ A := by rw [hAdef]; positivity
  have hR0 : 0 ≤ R := by rw [hRdef]; positivity
  have hR1 : R ≤ 1 := by rw [hRdef]; linarith
  obtain ⟨hVP1, hVP2⟩ := SCT.accel_VP hA0 hR0 hR1 e40 e41
  -- `t₁₅`
  set q := SCT.t15F L (E 14) with hq
  set t15 := eff q.toReal with ht15
  set N := SC.node Jm.toReal tj.toReal (eff t2.toReal) (eff t4.toReal) t15 with hN
  set tE := SC.tEnd Jm.toReal tj.toReal (eff t2.toReal) (eff t4.toReal) t15 with htE
  have n7 : N 7 = ⟨0, A * (R + eff t4.toReal), A * (R + eff t4.toReal) * (2 * R + eff t4.toReal) / 2⟩ := by
    rw [hN, SC.node_7_eq (by linarith)]
  have V7eq : (N 7).v = A * (R + eff t4.toReal) := by rw [n7]
  have P7eq : (N 7).p = A * (R + eff t4.toReal) * (2 * R + eff t4.toReal) / 2 := by rw [n7]
  have hp7' : SC.p7 A R (eff t4.toReal) = (N 7).p := by rw [P7eq]; rfl
  rw [hp7'] at hp7
  have hV70 : 0 ≤ (N 7).v := by rw [V7eq]; positivity
  have hP7L : (N 7).p ≤ (L.toReal / 2 + 11 / 10 ^ 8) * (1 + 1 / 1000) := by
    have := (abs_le.1 hLh).2
    linarith
  have hP7le : (N 7).p ≤ 1812 / 1000 := by linarith
  have hP70 : 0 ≤ (N 7).p := by rw [P7eq]; positivity
  have hVV : (N 7).v ^ 2 ≤ 2 * A * (N 7).p := by rw [V7eq, P7eq]; exact hVP1
  have hPV : (N 7).p ≤ 5 / 2 * (N 7).v := by rw [V7eq, P7eq]; exact hVP2
  have hAP : 2 * A * (N 7).p ≤ 2 * 2 * (N 7).p := by
    have := mul_le_mul_of_nonneg_right hA hP70; linarith
  have hV7le : (N 7).v ≤ 27 / 10 := SCT.le_of_sq_le hV70 (hVV.trans hAP) (by norm_num) (by linarith)
  have hPI : SC.ProfIn Jm.toReal tj.toReal (eff t2.toReal) (eff t4.toReal) t15 :=
    ⟨hJ0, hJ1, htj0, htj1, e20, e21, e40, e41, eff_nonneg _, hA, by
      have := V7eq; rw [hAdef, hRdef] at this; rw [← this]; linarith⟩
  -- the accelerating phase
  have h0' : SCT.Near (E 0) 0 ⟨0, 0, 0⟩ 0 0 0 0 := by
    rw [hE0]
    obtain ⟨a, b, c, d⟩ := h0
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
      simp only [a, b, c, d, f32_isFinite_0p0, f32_toReal_0p0, sub_zero, abs_zero, le_refl]
  obtain ⟨s1, s2, s3, s4, s5, s6, s7⟩ := SCT.accel_G hL hEs h0' fJ ft ft2 ft4 hPI
    (by linarith) (by linarith)
  have c8 := SCT.copy_step hEs (k := 7) (by norm_num) (by norm_num) s7
  have s8 : SCT.Near (E 8) (tE 8) (N 8) (21 / 10000000) 0 (111 / 10000000) (169 / 5000000) := c8.1
  have c9 := SCT.copy_step hEs (k := 8) (by norm_num) (by norm_num) s8
  have s9 : SCT.Near (E 9) (tE 9) (N 9) (21 / 10000000) 0 (111 / 10000000) (169 / 5000000) := c9.1
  have c10 := SCT.copy_step hEs (k := 9) (by norm_num) (by norm_num) s9
  have s10 : SCT.Near (E 10) (tE 10) (N 10) (21 / 10000000) 0 (111 / 10000000) (169 / 5000000) := c10.1
  have c11 := SCT.copy_step hEs (k := 10) (by norm_num) (by norm_num) s10
  have s11 : SCT.Near (E 11) (tE 11) (N 11) (21 / 10000000) 0 (111 / 10000000) (169 / 5000000) := c11.1
  have c12 := SCT.copy_step hEs (k := 11) (by norm_num) (by norm_num) s11
  have s12 : SCT.Near (E 12) (tE 12) (N 12) (21 / 10000000) 0 (111 / 10000000) (169 / 5000000) := c12.1
  have c13 := SCT.copy_step hEs (k := 12) (by norm_num) (by norm_num) s12
  have s13 : SCT.Near (E 13) (tE 13) (N 13) (21 / 10000000) 0 (111 / 10000000) (169 / 5000000) := c13.1
  have c14 := SCT.copy_step hEs (k := 13) (by norm_num) (by norm_num) s13
  have s14 : SCT.Near (E 14) (tE 14) (N 14) (21 / 10000000) 0 (111 / 10000000) (169 / 5000000) := c14.1
  have n14 : N 14 = N 7 := SC.node_14
  -- `t₁₅` from entry `14`
  have a7 : (N 7).a = 0 := by rw [n7]
  rw [n14] at s14
  have hP14 := s14.2.2.2.2
  have hV14 := s14.2.2.1.2
  have hP70 : 0 ≤ (N 7).p := SC.pos_nonneg hPI (by norm_num)
  have hLh1 := abs_le.1 hLh
  have hV7lo : 3 / 10 ^ 5 ≤ (N 7).v := by
    rcases hlow with h | h
    · rw [hp7'] at h; linarith
    · rw [V7eq]; linarith
  obtain ⟨fq, hq0, hqV⟩ := SCT.t15_spec fL s14.fin.2.2.2 s14.fin.2.2.1 (by linarith) (by linarith)
    (by rw [abs_le]; constructor <;> linarith [(abs_le.1 hP14).1, (abs_le.1 hP14).2])
    (by linarith [(abs_le.1 hV14).1]) (by linarith [(abs_le.1 hV14).2])
  have n22 : N 22 = ⟨0, 0, 2 * (N 7).p + (N 7).v * t15⟩ := by rw [hN]; exact SC.node_22_eq (by linarith)
  have key : t15 ≤ 15 ∧ 2 * (N 7).p + (N 7).v * t15 ≤ L.toReal * (1 + 1 / 1000) + 1 / 10 ^ 4 := by
    rcases Bool.eq_false_or_eq_true (is_positive_float q) with hp | hp
    · obtain ⟨he, hlo⟩ := SCT.eff_pos fq hp
      have ht : t15 = q.toReal := he
      rw [ht]
      have hQ0 : 0 < q.toReal := lt_of_lt_of_le (by norm_num) hlo
      have hVQ : (E 14).end_vel.toReal * q.toReal ≤ L.toReal - 2 * (E 14).end_pos.toReal + 2 / 10 ^ 6 :=
        by linarith [(abs_le.1 (hqV hQ0)).2]
      have hVpos : 0 < (E 14).end_vel.toReal := by linarith [(abs_le.1 hV14).1]
      rcases hlow with h | h
      · rw [hp7'] at h
        by_cases hLs : 3 / 100 ≤ L.toReal
        · -- regime `G`
          have hQ1 := SCT.q_le_low (K := 1) hLh h hPV hP14 hV14 hVQ hVpos (by norm_num)
            (by norm_num; linarith)
          have := SCT.final_core hQ0.le hP14 hV14 hVQ
          constructor <;> nlinarith
        · -- regime `S`: the small legs
          have hP7S : (N 7).p ≤ 1502 / 100000 := by linarith
          have hV7S : (N 7).v ≤ 2451 / 10000 := SCT.le_of_sq_le hV70 (hVV.trans hAP) (by norm_num)
            (by linarith)
          obtain ⟨-, -, -, -, -, -, t7⟩ := SCT.accel_S hL hEs h0' fJ ft ft2 ft4 hPI hV7S hP7S
          have t8 : SCT.Near (E 8) (tE 8) (N 8) (21 / 10000000) 0 (431 / 50000000) (203 / 10000000) :=
            (SCT.copy_step hEs (k := 7) (by norm_num) (by norm_num) t7).1
          have t9 : SCT.Near (E 9) (tE 9) (N 9) (21 / 10000000) 0 (431 / 50000000) (203 / 10000000) :=
            (SCT.copy_step hEs (k := 8) (by norm_num) (by norm_num) t8).1
          have t10 : SCT.Near (E 10) (tE 10) (N 10) (21 / 10000000) 0 (431 / 50000000) (203 / 10000000) :=
            (SCT.copy_step hEs (k := 9) (by norm_num) (by norm_num) t9).1
          have t11 : SCT.Near (E 11) (tE 11) (N 11) (21 / 10000000) 0 (431 / 50000000) (203 / 10000000) :=
            (SCT.copy_step hEs (k := 10) (by norm_num) (by norm_num) t10).1
          have t12 : SCT.Near (E 12) (tE 12) (N 12) (21 / 10000000) 0 (431 / 50000000) (203 / 10000000) :=
            (SCT.copy_step hEs (k := 11) (by norm_num) (by norm_num) t11).1
          have t13 : SCT.Near (E 13) (tE 13) (N 13) (21 / 10000000) 0 (431 / 50000000) (203 / 10000000) :=
            (SCT.copy_step hEs (k := 12) (by norm_num) (by norm_num) t12).1
          have t14 : SCT.Near (E 14) (tE 14) (N 14) (21 / 10000000) 0 (431 / 50000000) (203 / 10000000) :=
            (SCT.copy_step hEs (k := 13) (by norm_num) (by norm_num) t13).1
          rw [n14] at t14
          have hQ3 := SCT.q_le_low (K := 3) hLh h hPV t14.2.2.2.2 t14.2.2.1.2 hVQ hVpos (by norm_num)
            (by norm_num; linarith)
          have := SCT.final_core hQ0.le t14.2.2.2.2 t14.2.2.1.2 hVQ
          constructor <;> nlinarith
      · -- `V₇ ≥ 1/4`
        rw [← V7eq] at h
        have h1 := SCT.q_le_fast hP70 h hP14 hV14 hVQ hQ0.le
        have := SCT.final_core hQ0.le hP14 hV14 hVQ
        constructor <;> nlinarith
    · obtain ⟨he, -⟩ := SCT.eff_neg fq hp
      have ht : t15 = 0 := he
      rw [ht]
      refine ⟨by norm_num, ?_⟩
      have := (abs_le.1 hLh).2
      nlinarith
  obtain ⟨hq15, hfinal⟩ := key
  -- entry `15`
  have tb14 : 0 ≤ tE 14 ∧ tE 14 ≤ 5 := ⟨SC.tEnd_nonneg hPI 14, (SC.tEnd_le hPI).1 14 le_rfl⟩
  have s15 : SCT.Near (E 15) (tE 15) (N 15) (33 / 10000000) 0 (113 / 10000000) (209 / 1000000) := by
    have ee : E 15 = SCT.constE (E 14) q 0.0 := by rw [hEs]; rfl
    have ne : N 15 = SC.constNode (N 14) 0 t15 := rfl
    have te : tE 15 = tE 14 + t15 := rfl
    rw [ee, ne, te, n14]
    rcases Bool.eq_false_or_eq_true (is_positive_float q) with hp | hp
    · obtain ⟨he, -⟩ := SCT.eff_pos fq hp
      have ht : t15 = q.toReal := he
      rw [ht] at hq15 ⊢
      have h := SCT.near_const0 (D := 15) (TM := 20) (AM := 0) (VM := 3001 / 1000) (PM := 4001 / 1000)
        s14 hp fq hq0 hq15 (SCT.mag_t (by linarith) (by linarith) le_rfl) (by norm_num) (by norm_num)
        (by rw [a7]; norm_num) (SCT.mag_v hV70 hV7le (by norm_num)) (SCT.mag_v hP70 hP7le (by norm_num))
        (fun a b c => SCT.fl_const15 hL s14.fin.2.1 s14.fin.2.2.1 s14.fin.2.2.2 fq hq0 hq15 a b c)
      exact h.mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · obtain ⟨he, -⟩ := SCT.eff_neg fq hp
      have ht : t15 = 0 := he
      rw [ht]
      exact (SCT.near_gated s14 hp _).mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  -- the decelerating phase
  have hP22 : (N 22).p ≤ 37 / 10 := by rw [n22]; dsimp only; linarith
  obtain ⟨s16, s17, s18, s19, s20, s21, s22⟩ := SCT.decel_G hL hEs fJ ft ft2 ft4 hPI hq15 hP22 s15
  have s0 : SCT.Near (E 0) (tE 0) (N 0) 0 0 0 0 := h0'
  rw [← n14] at s14
  have hNear : ∀ k ≤ 22, SCT.Near (E k) (tE k) (N k) (2 / 10 ^ 5) (1 / 10 ^ 5) (3 / 10 ^ 5)
      (if k ≤ 14 then 4 / 10 ^ 5 else 4 / 10 ^ 4) := by
    intro k hk
    interval_cases k
    · exact s0.mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact s1.mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact s2.mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact s3.mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact s4.mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact s5.mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact s6.mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact s7.mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact s8.mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact s9.mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact s10.mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact s11.mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact s12.mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact s13.mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact s14.mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact s15.mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact s16.mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact s17.mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact s18.mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact s19.mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact s20.mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact s21.mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)
    · exact s22.mono (by norm_num) (by norm_num) (by norm_num) (by norm_num)
  have htE : ∀ k ≤ 22, 0 ≤ tE k ∧ tE k ≤ 25 := fun k hk =>
    ⟨SC.tEnd_nonneg hPI k, by linarith [(SC.tEnd_le hPI).2 k hk]⟩
  have h15 : t15 = eff q.toReal ∧ q.IsFinite ∧ (is_positive_float q = true → q.toReal ≤ 15) :=
    ⟨rfl, fq, fun hp => by have := (SCT.eff_pos fq hp).1; rw [← this]; exact hq15⟩
  refine ⟨t15, eff_nonneg _, hq15, hPI,
    tableOk_of hEs hnum hArr (hE0 ▸ hj0) fJ ft ft2 ft4 htj0 htj1 ht21 ht41 h15 htE hNear
      (by rw [hEs]; exact ⟨rfl, rfl⟩), ?_⟩
  change (N 22).p ≤ _
  rw [n22]
  exact hfinal

end

end Contracts.Mission