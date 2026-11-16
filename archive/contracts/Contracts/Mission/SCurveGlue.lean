import Contracts.Mission.SCurveTable
import Contracts.Mission.SCurveEval
import Contracts.Mission.SCurveGlueCase

/-!
# The S-curve position in `float` follows the real profile

`SCurve::get_jerk_accel_vel_pos_at_time` selects the segment whose `float` end times bracket the
time and evaluates its closed form in `float`. On a table that approximates the real profile
(`TableOk`), the position it returns is within `3/2000` of `SC.profPos` at the same time
(`eval_near`), for every time in `[0, 1000]`.
-/

namespace Contracts.Mission

open Float.Model UnpackedFloat AC_WPNav_lib

noncomputable section

/-- After `add_segments`, entry `14` (the copy of entry `7`, whose acceleration the code zeroes)
has acceleration exactly `0`. -/
theorem table_a14 (s : SCurve.State) (L : Float32) (hsz : s.segment.size = 23)
    (hn : s.num_segs = 1) (hz : is_zero_float L = false) :
    (SCurve.add_segments s L).segment[14]!.end_accel = 0.0 := by
  rcases h : SCurve.calculate_path s.snap_max s.jerk_max 0.0 s.accel_max s.vel_max (L * 0.5)
      0.0 0.0 0.0 0.0 0.0 with ⟨Jm, tj, t2, t4, t6⟩
  rw [(SCT.add_segments_tbl s L hsz hn hz h).2.2 14 (by norm_num)]
  generalize hE : SCT.tbl s.segment[0]! L Jm tj t2 t4 t6 = E
  have hEs : ∀ k, E (k + 1) = SCT.stepE L Jm tj t2 t4 t6 k (E k) := fun k => by rw [← hE]; rfl
  -- entries `8 … 14` copy entry `7`, whose acceleration the code zeroes
  have e : ∀ k, 7 ≤ k → k < 14 → (E (k + 1)).end_accel = (E k).end_accel := by
    intro k h1 h2
    rw [hEs]
    interval_cases k <;> exact (SCT.constE_neg SCT.isPos_zero).2.1
  have e7 : (E 7).end_accel = 0.0 := by rw [hEs]; rfl
  rw [e 13 (by norm_num) (by norm_num), e 12 (by norm_num) (by norm_num),
    e 11 (by norm_num) (by norm_num), e 10 (by norm_num) (by norm_num),
    e 9 (by norm_num) (by norm_num), e 8 (by norm_num) (by norm_num),
    e 7 (by norm_num) (by norm_num), e7]

/-- **The evaluated position follows the profile.** -/
theorem eval_near (hL : LibmSpec) {S : SCurve.State} {J tj t2 t4 t15 : ℝ}
    (hT : TableOk S J tj t2 t4 t15) (hP : SC.ProfIn J tj t2 t4 t15) (h15 : t15 ≤ 15)
    (h22 : (SC.node J tj t2 t4 t15 22).p ≤ 4) (ha14 : S.segment[14]!.end_accel = 0.0)
    {t : Float32} (ft : t.IsFinite) (ht0 : 0 ≤ t.toReal) (ht1 : t.toReal ≤ 1000) :
    (SCurve.get_jerk_accel_vel_pos_at_time S t 0.0 0.0 0.0 0.0).2.2.2.IsFinite ∧
      |(SCurve.get_jerk_accel_vel_pos_at_time S t 0.0 0.0 0.0 0.0).2.2.2.toReal -
        SC.profPos J tj t2 t4 t15 t.toReal| ≤ 3 / 2000 := by
  obtain ⟨k, hk, hinv, heq⟩ := SCG.get_sel S t hT.num
  have hpos : 0 ≤ SC.profPos J tj t2 t4 t15 t.toReal := by
    rw [← SC.profPos_of_le hP (le_refl 0)]; exact SC.profPos_mono hP ht0
  have hk' : (UInt8.ofNat k).toNat = k := SCG.idx_f ⟨k, by omega⟩
  unfold SCG.SelInv at hinv
  rw [hk'] at hinv
  have fT : ∀ j < 23, S.segment[j]!.end_time.IsFinite := fun j hj => (hT.fin j hj).1
  have key : (SCG.postP S t k).IsFinite ∧
      |(SCG.postP S t k).toReal - SC.profPos J tj t2 t4 t15 t.toReal| ≤ 3 / 2000 := by
    rcases hinv with ⟨h1, -, h3, h4⟩ | ⟨h1, h2⟩
    · have flt := (Float32.lt_iff_toReal_lt ft (fT k h1)).1 h3
      rcases k with _ | j
      · exact SCG.case_zero hT hP ft ht0 flt
      · have hle : S.segment[j]!.end_time.toReal ≤ t.toReal := not_lt.1 fun h =>
          h4 j (by omega) (by omega) ((Float32.lt_iff_toReal_lt ft (fT j (by omega))).2 h)
        exact SCG.case_mid hL hT hP h15 h22 ha14 (by omega) ft ht1 hle flt
    · subst h1
      have hge : S.segment[22]!.end_time.toReal ≤ t.toReal := not_lt.1 fun h =>
        h2 22 (by omega) (by omega) ((Float32.lt_iff_toReal_lt ft (fT 22 (by omega))).2 h)
      exact SCG.case_last hT hP h22 ft ht1 hge
  rw [heq]
  obtain ⟨hf, hb⟩ := key
  obtain ⟨hmf, hmv⟩ := wp_max_spec f32_isFinite_0p0 hf
  refine ⟨hmf, ?_⟩
  rw [hmv, f32_toReal_0p0]
  exact (SCG.max_close hpos).trans hb

end

end Contracts.Mission
