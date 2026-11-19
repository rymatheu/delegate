import Contracts.Mission.SCurveEval

/-!
# Glue for `SCurve::get_jerk_accel_vel_pos_at_time`: the selection loop

With `num_segs = 23` the selection loop of `get_jerk_accel_vel_pos_at_time` leaves the smallest
index `k` whose end time exceeds the time (or `23`), and the returned position is
`MAX(0, postP S t k)` (`get_sel`). `eval_const_abs`: `eval_const` at a local time of either sign
(the time before the first end time gives a negative local time).
-/

namespace Contracts.Mission

open Float.Model UnpackedFloat AC_WPNav_lib

namespace SCG

theorem forIn_foldl {β : Type} (n : ℕ) (b : β) (f : ℕ → β → Id (ForInStep β)) (g : ℕ → β → β)
    (hf : ∀ x b, f x b = ForInStep.yield (g x b)) :
    (forIn [:n] b f : Id β) = List.foldl (fun b x => g x b) b (List.range' 0 n) := by
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  have : f = fun a b => pure (ForInStep.yield (g a b)) := funext fun a => funext fun b => hf a b
  subst this
  rw [List.forIn_pure_yield_eq_foldl]
  simp [Std.Legacy.Range.size]

theorem idx_a : ∀ x : Fin 23,
    ((UInt8.toUInt32 23).toInt32 - 1 - (x.val).toUInt8.toUInt32.toInt32).toNatClampNeg = 22 - x.val := by
  decide +kernel
theorem idx_b : ∀ x : Fin 23,
    ((UInt8.toUInt32 23).toInt32 - 1 - (x.val).toUInt8.toUInt32.toInt32).toInt8.toUInt8.toNat = 22 - x.val := by
  decide +kernel
theorem idx_c : ∀ k : Fin 24, ((UInt8.ofNat k.val).toUInt32.toInt32 == 0) = decide (k.val = 0) := by
  decide +kernel
theorem idx_d : ∀ k : Fin 24, ((UInt8.ofNat k.val).toUInt32.toInt32 == (UInt8.toUInt32 23).toInt32) =
    decide (k.val = 23) := by
  decide +kernel
theorem idx_e : ∀ k : Fin 24, ((UInt8.ofNat k.val).toUInt32.toInt32 - 1).toNatClampNeg = k.val - 1 := by
  decide +kernel
theorem idx_f : ∀ k : Fin 24, (UInt8.ofNat k.val).toNat = k.val := by
  decide +kernel
theorem seg_max : ((UInt8.toUInt32 23).toInt32 != SCurve.segments_max.toUInt32.toInt32) = false := by
  decide +kernel


/-- The selection invariant after `m` passes. -/
def SelInv (c : ℕ → Prop) (m : ℕ) (p : UInt8) : Prop :=
  (p.toNat < 23 ∧ 23 - m ≤ p.toNat ∧ c p.toNat ∧ ∀ j, 23 - m ≤ j → j < p.toNat → ¬ c j) ∨
    (p.toNat = 23 ∧ ∀ j, 23 - m ≤ j → j < 23 → ¬ c j)

theorem sel_inv (c : ℕ → Prop) (g : ℕ → UInt8 → UInt8)
    (hg : ∀ x < 23, ∀ s, (c (22 - x) → (g x s).toNat = 22 - x) ∧ (¬ c (22 - x) → g x s = s)) :
    ∀ m ≤ 23, SelInv c m (List.foldl (fun b x => g x b) 23 (List.range' 0 m)) := by
  intro m
  induction m with
  | zero => intro _; right; exact ⟨rfl, fun j h1 h2 => by omega⟩
  | succ m ih =>
    intro hm
    have ih := ih (by omega)
    rw [List.range'_concat, List.foldl_append]
    simp only [List.foldl_cons, List.foldl_nil, Nat.zero_add, Nat.one_mul]
    generalize List.foldl (fun b x => g x b) 23 (List.range' 0 m) = p at ih ⊢
    obtain ⟨h1, h2⟩ := hg m (by omega) p
    by_cases hc : c (22 - m)
    · left
      rw [h1 hc]
      exact ⟨by omega, by omega, hc, fun j hj1 hj2 => by omega⟩
    · rw [h2 hc]
      have hj : ∀ j, 23 - (m + 1) ≤ j → j < 23 - m → ¬ c j := fun j hj1 hj2 => by
        obtain rfl : j = 22 - m := by omega
        exact hc
      rcases ih with ⟨i1, i2, i3, i4⟩ | ⟨i1, i2⟩
      · left
        refine ⟨i1, by omega, i3, fun j hj1 hj2 => ?_⟩
        rcases lt_or_ge j (23 - m) with h | h
        · exact hj j hj1 h
        · exact i4 j h hj2
      · right
        refine ⟨i1, fun j hj1 hj2 => ?_⟩
        rcases lt_or_ge j (23 - m) with h | h
        · exact hj j hj1 h
        · exact i2 j h hj2

/-- The position the code computes once the loop has selected `k`. -/
def postP (S : SCurve.State) (t : Float32) (k : ℕ) : Float32 :=
  if k = 0 then
    (SCurve.calc_javp_for_segment_const_jerk (t - S.segment[0]!.end_time) 0.0
      S.segment[0]!.end_accel S.segment[0]!.end_vel S.segment[0]!.end_pos 0.0 0.0 0.0 0.0).2.2.2
  else if k = 23 then
    (SCurve.calc_javp_for_segment_const_jerk (t - S.segment[22]!.end_time) 0.0
      S.segment[22]!.end_accel S.segment[22]!.end_vel S.segment[22]!.end_pos 0.0 0.0 0.0 0.0).2.2.2
  else
    match S.segment[k]!.seg_type with
    | .CONSTANT_JERK =>
      (SCurve.calc_javp_for_segment_const_jerk (t - S.segment[k - 1]!.end_time)
        S.segment[k]!.jerk_ref S.segment[k - 1]!.end_accel S.segment[k - 1]!.end_vel
        S.segment[k - 1]!.end_pos 0.0 0.0 0.0 0.0).2.2.2
    | .POSITIVE_JERK =>
      (SCurve.calc_javp_for_segment_incr_jerk (t - S.segment[k - 1]!.end_time)
        (S.segment[k]!.end_time - S.segment[k - 1]!.end_time)
        S.segment[k]!.jerk_ref S.segment[k - 1]!.end_accel S.segment[k - 1]!.end_vel
        S.segment[k - 1]!.end_pos 0.0 0.0 0.0 0.0).2.2.2
    | .NEGATIVE_JERK =>
      (SCurve.calc_javp_for_segment_decr_jerk (t - S.segment[k - 1]!.end_time)
        (S.segment[k]!.end_time - S.segment[k - 1]!.end_time)
        S.segment[k]!.jerk_ref S.segment[k - 1]!.end_accel S.segment[k - 1]!.end_vel
        S.segment[k - 1]!.end_pos 0.0 0.0 0.0 0.0).2.2.2

/-- One pass of the selection loop. -/
def selG (S : SCurve.State) (t : Float32) (i' : ℕ) (s : UInt8) : UInt8 :=
  if t < S.segment[((UInt8.toUInt32 23).toInt32 - 1 - i'.toUInt8.toUInt32.toInt32).toNatClampNeg]!.end_time
  then ((UInt8.toUInt32 23).toInt32 - 1 - i'.toUInt8.toUInt32.toInt32).toInt8.toUInt8 else s

set_option maxHeartbeats 4000000 in
theorem get_sel (S : SCurve.State) (t : Float32) (hn : S.num_segs = 23) :
    ∃ k ≤ 23, SelInv (fun j => t < S.segment[j]!.end_time) 23 (UInt8.ofNat k) ∧
      (SCurve.get_jerk_accel_vel_pos_at_time S t 0.0 0.0 0.0 0.0).2.2.2 =
        MAX_float2 0.0 (postP S t k) := by
  unfold SCurve.get_jerk_accel_vel_pos_at_time
  simp only [hn]
  rw [seg_max]
  simp only [Bool.false_eq_true, ite_false]
  rw [show UInt8.toNat 23 = 23 from rfl, forIn_foldl _ _ _ (selG S t) ?hf]
  case hf =>
    intro x b
    unfold selG
    split <;> rfl
  have hinv := sel_inv (fun j => t < S.segment[j]!.end_time) (selG S t) (by
    intro x hx s
    have ha := idx_a ⟨x, hx⟩
    have hb := idx_b ⟨x, hx⟩
    simp only at ha hb
    unfold selG
    rw [ha]
    constructor
    · intro h; simp only [h, ↓reduceIte]; exact hb
    · intro h; simp only [h, ↓reduceIte]) 23 le_rfl
  generalize List.foldl (fun b x => selG S t x b) (23 : UInt8) (List.range' 0 23) = p at hinv ⊢
  have hk : p.toNat ≤ 23 := by rcases hinv with h | h <;> omega
  have hp : p = UInt8.ofNat p.toNat := by simp
  refine ⟨p.toNat, hk, by rw [← hp]; exact hinv, ?_⟩
  generalize p.toNat = k at hk hp
  subst hp
  have c1 := idx_c ⟨k, by omega⟩
  have c2 := idx_d ⟨k, by omega⟩
  have c3 := idx_e ⟨k, by omega⟩
  have c4 := idx_f ⟨k, by omega⟩
  simp only at c1 c2 c3 c4
  rw [id_bind_eq]
  simp only [c1, c2, c3, c4, postP]
  by_cases h0 : k = 0
  · subst h0; simp
  by_cases h23 : k = 23
  · subst h23; simp
  simp only [h0, h23, decide_false, ite_false]
  rcases S.segment[k]!.seg_type <;> rfl


macro "sce_side'" : tactic => `(tactic| first | (norm_num; done) | linarith | nlinarith)

set_option maxHeartbeats 4000000 in
/-- `eval_const` at a local time of either sign. -/
theorem eval_const_abs {τ J0 A0 V0 P0 Jt At Vt Pt : Float32} (fτ : τ.IsFinite) (fJ : J0.IsFinite)
    (fA : A0.IsFinite) (fV : V0.IsFinite) (fP : P0.IsFinite)
    (hτ1 : |τ.toReal| ≤ 2 ^ 10) (hJ : |J0.toReal| * |τ.toReal| ^ 3 ≤ 64)
    (hA : |A0.toReal| * |τ.toReal| ^ 2 ≤ 64) (hV : |V0.toReal| * |τ.toReal| ≤ 64)
    (hP : |P0.toReal| ≤ 64) (hJb : |J0.toReal| ≤ 2 ^ 20) (hAb : |A0.toReal| ≤ 2 ^ 20) :
    (SCurve.calc_javp_for_segment_const_jerk τ J0 A0 V0 P0 Jt At Vt Pt).2.2.2.IsFinite ∧
      |(SCurve.calc_javp_for_segment_const_jerk τ J0 A0 V0 P0 Jt At Vt Pt).2.2.2.toReal -
        SC.cP ⟨A0.toReal, V0.toReal, P0.toReal⟩ J0.toReal τ.toReal| ≤
        16 / 16777216 * (|P0.toReal| + |V0.toReal| * |τ.toReal| + |A0.toReal| * |τ.toReal| ^ 2 +
          |J0.toReal| * |τ.toReal| ^ 3) + 1 / 2 ^ 100 := by
  have hPt : (SCurve.calc_javp_for_segment_const_jerk τ J0 A0 V0 P0 Jt At Vt Pt).2.2.2 =
      P0 + V0 * τ + (0.5 : Float32) * A0 * (τ * τ) + (0.166666672 : Float32) * J0 * (τ * τ * τ) := by
    rw [← sce_c6]; rfl
  rw [hPt]
  generalize ht : τ.toReal = t at *
  generalize hw : |t| = w at *
  have hw0 : 0 ≤ w := by rw [← hw]; exact abs_nonneg t
  have hww : t * t = w * w := by rw [← hw, abs_mul_abs_self]
  have hwww : |t * t * t| = w * w * w := by rw [← hw, abs_mul, abs_mul]
  have eT : SCE32 τ t w 0 0 := SCE32.lit fτ ht (by rw [hw])
  have eV := SCE32.lit fV rfl le_rfl
  have eP := SCE32.lit fP rfl le_rfl
  have eA := SCE32.lit fA rfl le_rfl
  have eJ := SCE32.lit fJ rfl le_rfl
  have eH : SCE32 (0.5 : Float32) (1 / 2) (1 / 2) 0 0 :=
    SCE32.lit f32_isFinite_0p5 f32_toReal_0p5 (by norm_num)
  have eC : SCE32 (0.166666672 : Float32) (1 / 6) (1 / 6) 1 0 :=
    ⟨sce_isFinite_c6, by rw [sce_toReal_c6]; norm_num, by norm_num⟩
  have ht2 : w * w ≤ 2 ^ 20 := by nlinarith
  have ht3 : w * w * w ≤ 2 ^ 30 := by nlinarith
  have hA0 := abs_nonneg A0.toReal
  have hJ0 := abs_nonneg J0.toReal
  have v1 : SCE32 (V0 * τ) (V0.toReal * t) (|V0.toReal| * w) 1 (1 / 2 ^ 150) := by
    apply SCE32.mul eV eT (da := 0) (db := 0) <;> sce_side'
  have s1 : SCE32 (P0 + V0 * τ) (P0.toReal + V0.toReal * t) (|P0.toReal| + |V0.toReal| * w) 3
      (1 / 2 ^ 149) := by
    apply SCE32.add eP v1 (K := 1) <;> sce_side'
  have h1 : SCE32 ((0.5 : Float32) * A0) (1 / 2 * A0.toReal) (1 / 2 * |A0.toReal|) 1 (1 / 2 ^ 150) := by
    apply SCE32.mul eH eA (da := 0) (db := 0) <;> sce_side'
  have q1 : SCE32 (τ * τ) (t * t) (w * w) 1 (1 / 2 ^ 150) := by
    apply SCE32.mul eT eT (da := 0) (db := 0) <;> sce_side'
  have t2 : SCE32 ((0.5 : Float32) * A0 * (τ * τ)) (1 / 2 * A0.toReal * (t * t))
      (1 / 2 * |A0.toReal| * (w * w)) 4 (1 / 2 ^ 128) := by
    apply SCE32.mul h1 q1 (da := 1 / 2 ^ 130) (db := 1 / 2 ^ 131) <;> sce_side'
  have s2 : SCE32 (P0 + V0 * τ + (0.5 : Float32) * A0 * (τ * τ))
      (P0.toReal + V0.toReal * t + 1 / 2 * A0.toReal * (t * t))
      (|P0.toReal| + |V0.toReal| * w + 1 / 2 * |A0.toReal| * (w * w)) 6 (1 / 2 ^ 127) := by
    apply SCE32.add s1 t2 (K := 4) <;> sce_side'
  have j1 : SCE32 ((0.166666672 : Float32) * J0) (1 / 6 * J0.toReal) (1 / 6 * |J0.toReal|) 3
      (1 / 2 ^ 150) := by
    apply SCE32.mul eC eJ (da := 0) (db := 0) <;> sce_side'
  have q3 : SCE32 (τ * τ * τ) (t * t * t) (w * w * w) 3 (1 / 2 ^ 139) := by
    apply SCE32.mul q1 eT (da := 1 / 2 ^ 140) (db := 0) <;> sce_side'
  have t3 : SCE32 ((0.166666672 : Float32) * J0 * (τ * τ * τ)) (1 / 6 * J0.toReal * (t * t * t))
      (1 / 6 * |J0.toReal| * (w * w * w)) 8 (1 / 2 ^ 118) := by
    apply SCE32.mul j1 q3 (da := 1 / 2 ^ 120) (db := 1 / 2 ^ 120) <;> sce_side'
  have s3 := SCE32.add s2 t3 (K := 8) (k := 10) (c := 1 / 2 ^ 117) (by norm_num) (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) (by nlinarith) (by norm_num) (by norm_num)
  refine ⟨s3.1, ?_⟩
  have hr : P0.toReal + V0.toReal * t + 1 / 2 * A0.toReal * (t * t) + 1 / 6 * J0.toReal * (t * t * t)
      = SC.cP ⟨A0.toReal, V0.toReal, P0.toReal⟩ J0.toReal t := by
    simp only [SC.cP]; ring
  have := s3.2.1
  rw [hr] at this
  have : 0 ≤ |A0.toReal| * (w * w) := by positivity
  have : 0 ≤ |J0.toReal| * (w * w * w) := by positivity
  have : 0 ≤ |V0.toReal| * w := by positivity
  have := abs_nonneg P0.toReal
  have e1 : w ^ 2 = w * w := by ring
  have e2 : w ^ 3 = w * w * w := by ring
  rw [e1, e2]
  linarith

end SCG

end Contracts.Mission
