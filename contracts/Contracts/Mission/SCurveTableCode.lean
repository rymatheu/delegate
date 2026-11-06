import Contracts.Mission.SCurveCalc

/-!
# `SCurve::add_segments` as a table of entries

The segment table written by `add_segments` (from a freshly initialized curve: one segment, the
`num_segs = 1`, array size `23`), as entries computed one from the previous: `constE`, `incrE`,
`decrE` are the entries written by `add_segment_const_jerk`, `add_segment_incr_jerk`,
`add_segment_decr_jerk` from the previous entry, and `tbl` the whole table
(`add_segments_tbl`).
-/

namespace Contracts.Mission

open AC_WPNav_lib

namespace SCT

/-- The entry `add_segment_const_jerk` writes after entry `p`. -/
def constE (p : SCurve.segment_t) (tin J0 : Float32) : SCurve.segment_t :=
  if is_positive_float tin then
    { jerk_ref := J0, seg_type := .CONSTANT_JERK, end_time := p.end_time + tin,
      end_accel := p.end_accel + J0 * tin,
      end_vel := p.end_vel + p.end_accel * tin + (0.5 : Float32) * J0 * sq_float tin,
      end_pos := p.end_pos + p.end_vel * tin + (0.5 : Float32) * p.end_accel * sq_float tin +
        ((1.0 : Float32) / (6.0 : Float32)) * J0 * Float32.pow tin (3.0 : Float32) }
  else
    { jerk_ref := J0, seg_type := .CONSTANT_JERK, end_time := p.end_time,
      end_accel := p.end_accel, end_vel := p.end_vel, end_pos := p.end_pos }

/-- `β = π / t_j` in `float`. -/
def betaF (tj : Float32) : Float32 := Float.toFloat32 (3.1415926535897931 : Float) / tj
/-- `VT` of the code. -/
def vtF (tj Jm : Float32) : Float32 :=
  Jm * (0.5 : Float32) * (sq_float tj * (0.5 : Float32) - (2.0 : Float32) / sq_float (betaF tj))
/-- `PT` of the code. -/
def ptF (tj Jm : Float32) : Float32 :=
  Jm * (0.5 : Float32) * ((-(1.0 : Float32) / sq_float (betaF tj)) * tj +
    ((1.0 : Float32) / (6.0 : Float32)) * Float32.pow tj (3.0 : Float32))
/-- `P2T` of the code. -/
def p2tF (tj Jm : Float32) : Float32 :=
  Jm * (0.5 : Float32) * ((-(1.0 : Float32) / sq_float (betaF tj)) * (2.0 : Float32) * tj +
    ((4.0 : Float32) / (3.0 : Float32)) * Float32.pow tj (3.0 : Float32))

/-- The entry `add_segment_incr_jerk` writes after entry `p`. -/
def incrE (p : SCurve.segment_t) (tj Jm : Float32) : SCurve.segment_t :=
  if is_positive_float tj then
    { jerk_ref := Jm, seg_type := .POSITIVE_JERK, end_time := p.end_time + tj,
      end_accel := p.end_accel + Jm * (0.5 : Float32) * tj,
      end_vel := p.end_vel + p.end_accel * tj + vtF tj Jm,
      end_pos := p.end_pos + p.end_vel * tj + (0.5 : Float32) * p.end_accel * sq_float tj +
        ptF tj Jm }
  else
    { jerk_ref := 0.0, seg_type := .CONSTANT_JERK, end_time := p.end_time,
      end_accel := p.end_accel, end_vel := p.end_vel, end_pos := p.end_pos }

/-- The entry `add_segment_decr_jerk` writes after entry `p`. -/
def decrE (p : SCurve.segment_t) (tj Jm : Float32) : SCurve.segment_t :=
  if is_positive_float tj then
    { jerk_ref := Jm, seg_type := .NEGATIVE_JERK, end_time := p.end_time + tj,
      end_accel := p.end_accel - Jm * (0.5 : Float32) * tj + Jm * tj,
      end_vel := p.end_vel - vtF tj Jm + (p.end_accel - Jm * (0.5 : Float32) * tj) * tj +
        Jm * sq_float tj,
      end_pos := p.end_pos - ptF tj Jm + (p.end_vel - vtF tj Jm) * tj +
        (0.5 : Float32) * (p.end_accel - Jm * (0.5 : Float32) * tj) * sq_float tj + p2tF tj Jm }
  else
    { jerk_ref := 0.0, seg_type := .CONSTANT_JERK, end_time := p.end_time,
      end_accel := p.end_accel, end_vel := p.end_vel, end_pos := p.end_pos }

/-- The constant-velocity time of `add_segments` from entry `14`. -/
def t15F (L : Float32) (e : SCurve.segment_t) : Float32 :=
  MAX_float2 (0.0 : Float32) ((L - (2.0 : Float32) * e.end_pos) / e.end_vel)

/-- Entry `k + 1` of the table from entry `k`. -/
def stepE (L Jm tj t2 t4 t6 : Float32) : ℕ → SCurve.segment_t → SCurve.segment_t
  | 0, e => incrE e tj Jm
  | 1, e => constE e t2 Jm
  | 2, e => decrE e tj Jm
  | 3, e => constE e t4 0.0
  | 4, e => incrE e tj (-Jm)
  | 5, e => constE e t6 (-Jm)
  | 6, e => { decrE e tj (-Jm) with end_accel := 0.0 }
  | 14, e => constE e (t15F L e) 0.0
  | 15, e => incrE e tj (-Jm)
  | 16, e => constE e t6 (-Jm)
  | 17, e => decrE e tj (-Jm)
  | 18, e => constE e t4 0.0
  | 19, e => incrE e tj Jm
  | 20, e => constE e t2 Jm
  | 21, e => { decrE e tj Jm with end_accel := 0.0, end_vel := 0.0 }
  | _, e => constE e 0.0 0.0

/-- **The table** of `add_segments` from the start entry `e0`. -/
def tbl (e0 : SCurve.segment_t) (L Jm tj t2 t4 t6 : Float32) : ℕ → SCurve.segment_t
  | 0 => e0
  | k + 1 => stepE L Jm tj t2 t4 t6 k (tbl e0 L Jm tj t2 t4 t6 k)

/-! ## Arrays -/

/-- The array `a` has size `23` and agrees with `E` below `k`. -/
def Arr (a : Array SCurve.segment_t) (k : ℕ) (E : ℕ → SCurve.segment_t) : Prop :=
  a.size = 23 ∧ ∀ j < k, a[j]! = E j

theorem Arr.set {a : Array SCurve.segment_t} {k : ℕ} {E : ℕ → SCurve.segment_t} (h : Arr a k E)
    (hk : k < 23) : Arr (a.set! k (E k)) (k + 1) E := by
  refine ⟨by simp [Array.set!, h.1], fun j hj => ?_⟩
  rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
  · rw [← h.2 j hj]
    simp [Array.set!, getElem!_def, (Nat.ne_of_lt hj).symm]
  · simp [Array.set!, h.1, hk]

theorem get_set_self (a : Array SCurve.segment_t) (j : ℕ) (x : SCurve.segment_t) (h : j < a.size) :
    (a.set! j x)[j]! = x := by simp [Array.set!, h]

theorem get_set_ne (a : Array SCurve.segment_t) (i j : ℕ) (x : SCurve.segment_t) (h : i ≠ j) :
    (a.set! i x)[j]! = a[j]! := by simp [Array.set!, getElem!_def, h]

theorem size_set (a : Array SCurve.segment_t) (j : ℕ) (x : SCurve.segment_t) :
    (a.set! j x).size = a.size := by simp [Array.set!]

theorem idx_aux : ∀ n : Fin 256, 1 ≤ n.val →
    Int32.toNatClampNeg (UInt32.toInt32 (UInt8.toUInt32 (UInt8.ofNat n.val)) - 1) = n.val - 1 := by
  decide +kernel

theorem idx_prev (i : UInt8) (h : 1 ≤ i.toNat) :
    Int32.toNatClampNeg (UInt32.toInt32 (UInt8.toUInt32 i) - 1) = i.toNat - 1 := by
  have := idx_aux ⟨i.toNat, i.toNat_lt⟩ h
  simpa using this

theorem add_segment_eq (s : SCurve.State) (i : UInt8) (T : Float32) (ty : SCurve.SegmentType)
    (J A V P : Float32) (h : i.toNat < s.segment.size) :
    SCurve.add_segment s i T ty J A V P =
      ({ s with segment := (s.segment.set! i.toNat
        { jerk_ref := J, seg_type := ty, end_time := T, end_accel := A, end_vel := V,
          end_pos := P }) }, i + 1) := by
  simp [SCurve.add_segment, Array.set!, h]

theorem const_eq (s : SCurve.State) (i : UInt8) (tin J0 : Float32) (h1 : 1 ≤ i.toNat)
    (h : i.toNat < s.segment.size) :
    SCurve.add_segment_const_jerk s i tin J0 =
      ({ s with segment := (s.segment.set! i.toNat
        (constE s.segment[i.toNat - 1]! tin J0)) }, i + 1) := by
  unfold SCurve.add_segment_const_jerk constE
  dsimp only [Id.run]
  rw [idx_prev _ h1]
  by_cases hp : is_positive_float tin = true
  · simp only [hp, Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
    rw [add_segment_eq _ _ _ _ _ _ _ _ h]
    rfl
  · simp only [hp, Bool.not_false, ite_true, Bool.false_eq_true, ite_false]
    rw [add_segment_eq _ _ _ _ _ _ _ _ h]
    rfl

theorem incr_eq (s : SCurve.State) (i : UInt8) (tj Jm : Float32) (h1 : 1 ≤ i.toNat)
    (h : i.toNat < s.segment.size) :
    SCurve.add_segment_incr_jerk s i tj Jm =
      ({ s with segment := (s.segment.set! i.toNat
        (incrE s.segment[i.toNat - 1]! tj Jm)) }, i + 1) := by
  unfold SCurve.add_segment_incr_jerk incrE
  dsimp only [Id.run]
  rw [idx_prev _ h1]
  by_cases hp : is_positive_float tj = true
  · simp only [hp, Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
    rw [add_segment_eq _ _ _ _ _ _ _ _ h]
    rfl
  · simp only [hp, Bool.not_false, ite_true, Bool.false_eq_true, ite_false]
    rw [add_segment_eq _ _ _ _ _ _ _ _ h]
    rfl

theorem decr_eq (s : SCurve.State) (i : UInt8) (tj Jm : Float32) (h1 : 1 ≤ i.toNat)
    (h : i.toNat < s.segment.size) :
    SCurve.add_segment_decr_jerk s i tj Jm =
      ({ s with segment := (s.segment.set! i.toNat
        (decrE s.segment[i.toNat - 1]! tj Jm)) }, i + 1) := by
  unfold SCurve.add_segment_decr_jerk decrE
  dsimp only [Id.run]
  rw [idx_prev _ h1]
  by_cases hp : is_positive_float tj = true
  · simp only [hp, Bool.not_true, Bool.false_eq_true, ite_false, ite_true]
    rw [add_segment_eq _ _ _ _ _ _ _ _ h]
    rfl
  · simp only [hp, Bool.not_false, ite_true, Bool.false_eq_true, ite_false]
    rw [add_segment_eq _ _ _ _ _ _ _ _ h]
    rfl

theorem jerk_eq (s : SCurve.State) (i : UInt8) (tj Jm T : Float32) (h1 : 1 ≤ i.toNat)
    (h : i.toNat + 2 < s.segment.size) (h255 : i.toNat + 2 < 256) :
    SCurve.add_segments_jerk s i tj Jm T =
      ({ s with segment := (((s.segment.set! i.toNat (incrE s.segment[i.toNat - 1]! tj Jm)).set!
        (i.toNat + 1) (constE (incrE s.segment[i.toNat - 1]! tj Jm) T Jm)).set! (i.toNat + 2)
          (decrE (constE (incrE s.segment[i.toNat - 1]! tj Jm) T Jm) tj Jm)) }, i + 1 + 1 + 1) := by
  have e1 : (i + 1).toNat = i.toNat + 1 := by
    rw [UInt8.toNat_add, UInt8.toNat_one]; exact Nat.mod_eq_of_lt (by omega)
  have e2 : (i + 1 + 1).toNat = i.toNat + 2 := by
    rw [UInt8.toNat_add, e1, UInt8.toNat_one]; exact Nat.mod_eq_of_lt (by omega)
  unfold SCurve.add_segments_jerk
  dsimp only [Id.run]
  rw [incr_eq _ _ _ _ h1 (by omega)]
  dsimp only
  rw [const_eq _ _ _ _ (by omega) (by simp [Array.set!, e1]; omega)]
  dsimp only
  rw [decr_eq _ _ _ _ (by omega) (by simp [Array.set!, e2]; omega)]
  have e3 : i.toNat + 2 - 1 = i.toNat + 1 := by omega
  simp only [e1, e2, e3, Nat.add_sub_cancel]
  have g1 : ((s.segment.set! i.toNat (incrE s.segment[i.toNat - 1]! tj Jm)))[i.toNat]! =
      incrE s.segment[i.toNat - 1]! tj Jm := get_set_self _ _ _ (by omega)
  have g2 : ((s.segment.set! i.toNat (incrE s.segment[i.toNat - 1]! tj Jm)).set! (i.toNat + 1)
      (constE (incrE s.segment[i.toNat - 1]! tj Jm) T Jm))[i.toNat + 1]! =
      constE (incrE s.segment[i.toNat - 1]! tj Jm) T Jm :=
    get_set_self _ _ _ (by rw [size_set]; omega)
  rw [g1, g2]
  rfl

theorem toNat_succ {i : UInt8} {k : ℕ} (hi : i.toNat = k) (hk : k + 1 < 256) : (i + 1).toNat = k + 1 := by
  rw [UInt8.toNat_add, UInt8.toNat_one, hi]; exact Nat.mod_eq_of_lt hk

theorem const_arr {S : SCurve.State} {i : UInt8} {k : ℕ} {E : ℕ → SCurve.segment_t}
    {tin J0 : Float32} {r : SCurve.State × UInt8}
    (hr : SCurve.add_segment_const_jerk S i tin J0 = r) (hA : Arr S.segment k E) (hi : i.toNat = k)
    (hk1 : 1 ≤ k) (hk : k < 23) (hE : E k = constE (E (k - 1)) tin J0) :
    Arr r.1.segment (k + 1) E ∧ r.2.toNat = k + 1 := by
  subst hr
  rw [const_eq _ _ _ _ (by omega) (by rw [hA.1]; omega)]
  refine ⟨?_, toNat_succ hi (by omega)⟩
  show Arr (S.segment.set! i.toNat (constE S.segment[i.toNat - 1]! tin J0)) (k + 1) E
  rw [hi, hA.2 _ (by omega), ← hE]
  exact hA.set hk

theorem jerk_arr {S : SCurve.State} {i : UInt8} {k : ℕ} {E : ℕ → SCurve.segment_t}
    {tj Jm T : Float32} {r : SCurve.State × UInt8}
    (hr : SCurve.add_segments_jerk S i tj Jm T = r) (hA : Arr S.segment k E) (hi : i.toNat = k)
    (hk1 : 1 ≤ k) (hk : k + 2 < 23) (hE1 : E k = incrE (E (k - 1)) tj Jm)
    (hE2 : E (k + 1) = constE (E k) T Jm) :
    Arr r.1.segment (k + 2) E ∧ r.1.segment[k + 2]! = decrE (E (k + 1)) tj Jm ∧
      r.2.toNat = k + 3 := by
  subst hr
  rw [jerk_eq _ _ _ _ _ (by omega) (by rw [hA.1]; omega) (by omega)]
  refine ⟨?_, ?_, ?_⟩
  · show Arr (((S.segment.set! i.toNat (incrE S.segment[i.toNat - 1]! tj Jm)).set!
      (i.toNat + 1) (constE (incrE S.segment[i.toNat - 1]! tj Jm) T Jm)).set! (i.toNat + 2)
        (decrE (constE (incrE S.segment[i.toNat - 1]! tj Jm) T Jm) tj Jm)) (k + 2) E
    rw [hi, hA.2 _ (by omega), ← hE1, ← hE2]
    have h1 := (hA.set (by omega)).set (by omega)
    refine ⟨by rw [size_set]; exact h1.1, fun j hj => ?_⟩
    rw [get_set_ne _ _ _ _ (by omega)]
    exact h1.2 j hj
  · show (((S.segment.set! i.toNat (incrE S.segment[i.toNat - 1]! tj Jm)).set!
      (i.toNat + 1) (constE (incrE S.segment[i.toNat - 1]! tj Jm) T Jm)).set! (i.toNat + 2)
        (decrE (constE (incrE S.segment[i.toNat - 1]! tj Jm) T Jm) tj Jm))[k + 2]! = _
    rw [hi, hA.2 _ (by omega), ← hE1, ← hE2]
    exact get_set_self _ _ _ (by rw [size_set, size_set, hA.1]; omega)
  · exact toNat_succ (toNat_succ (toNat_succ hi (by omega)) (by omega)) (by omega)

/-- Arr extends by an entry already in place. -/
theorem Arr.of_get {a : Array SCurve.segment_t} {k : ℕ} {E : ℕ → SCurve.segment_t}
    (h : Arr a k E) (hk : a[k]! = E k) : Arr a (k + 1) E :=
  ⟨h.1, fun j hj => by
    rcases Nat.lt_succ_iff_lt_or_eq.1 hj with hj | rfl
    · exact h.2 j hj
    · exact hk⟩

end SCT

end Contracts.Mission

namespace Contracts.Mission.SCT

open AC_WPNav_lib

theorem forIn7 {β : Type} (b : β) (f : ℕ → β → Id (ForInStep β)) (g : β → β)
    (hf : ∀ x b, f x b = ForInStep.yield (g b)) :
    (forIn [:7] b f : Id β) = g (g (g (g (g (g (g b)))))) := by
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size, List.range',
    List.forIn_cons, List.forIn_nil, hf]
  rfl

/-- One pass of the loop of `add_segments`: an empty constant segment. -/
def zstep (s : SCurve.State) : SCurve.State :=
  { (SCurve.add_segment_const_jerk s s.num_segs 0.0 0.0).1 with
    num_segs := (SCurve.add_segment_const_jerk s s.num_segs 0.0 0.0).2 }

theorem zstep_arr {S : SCurve.State} {k : ℕ} {E : ℕ → SCurve.segment_t} (hA : Arr S.segment k E)
    (hi : S.num_segs.toNat = k) (hk1 : 1 ≤ k) (hk : k < 23) (hE : E k = constE (E (k - 1)) 0.0 0.0) :
    Arr (zstep S).segment (k + 1) E ∧ (zstep S).num_segs.toNat = k + 1 := by
  have := const_arr (S := S) (i := S.num_segs) (tin := 0.0) (J0 := 0.0)
    (r := SCurve.add_segment_const_jerk S S.num_segs 0.0 0.0) rfl hA hi hk1 hk hE
  dsimp only [zstep]
  exact this

theorem setA_arr {a : Array SCurve.segment_t} {n : ℕ} {E : ℕ → SCurve.segment_t} {x : SCurve.segment_t}
    (hA : Arr a n E) (hn : n < 23) (hg : a[n]! = x) (hE : E n = { x with end_accel := 0.0 }) :
    Arr (a.set! n { a[n]! with end_accel := 0.0 }) (n + 1) E := by
  rw [hg, ← hE]; exact hA.set hn

theorem setAV_arr {a : Array SCurve.segment_t} {n : ℕ} {E : ℕ → SCurve.segment_t} {x : SCurve.segment_t}
    (hA : Arr a n E) (hn : n < 23) (hg : a[n]! = x)
    (hE : E n = { x with end_accel := 0.0, end_vel := 0.0 }) :
    Arr ((a.set! n { a[n]! with end_accel := 0.0 }).set! n
      { (a.set! n { a[n]! with end_accel := 0.0 })[n]! with end_vel := 0.0 }) (n + 1) E := by
  rw [get_set_self _ _ _ (by rw [hA.1]; exact hn), hg]
  have h1 : (a.set! n { x with end_accel := 0.0 }).set! n
      { x with end_accel := 0.0, end_vel := 0.0 } = a.set! n (E n) := by
    rw [hE]; simp [Array.set!]
  rw [h1]; exact hA.set hn

end Contracts.Mission.SCT

namespace Contracts.Mission.SCT

open AC_WPNav_lib

/-- The final state of `add_segments` holds the table `E`. -/
def TabQ (E : ℕ → SCurve.segment_t) (R : SCurve.State) : Prop :=
  R.num_segs.toNat = 23 ∧ Arr R.segment 23 E

set_option maxHeartbeats 1000000 in
/-- **`add_segments` writes the table `tbl`.** -/
theorem add_segments_tbl (s : SCurve.State) (L : Float32) (hsz : s.segment.size = 23)
    (hn : s.num_segs = 1) (hz : is_zero_float L = false) {Jm tj t2 t4 t6 : Float32}
    (hcp : SCurve.calculate_path s.snap_max s.jerk_max 0.0 s.accel_max s.vel_max (L * 0.5)
      0.0 0.0 0.0 0.0 0.0 = (Jm, tj, t2, t4, t6)) :
    TabQ (tbl s.segment[0]! L Jm tj t2 t4 t6) (SCurve.add_segments s L) := by
  generalize hE : tbl s.segment[0]! L Jm tj t2 t4 t6 = E
  have hEs : ∀ k, E (k + 1) = stepE L Jm tj t2 t4 t6 k (E k) := fun k => by rw [← hE]; rfl
  have A0 : Arr s.segment 1 E := ⟨hsz, fun j hj => by
    obtain rfl : j = 0 := by omega
    rw [← hE]; rfl⟩
  have hn' : s.num_segs.toNat = 1 := by rw [hn]; rfl
  unfold SCurve.add_segments
  rw [hz, ite_eq_right Bool.false_ne_true]
  dsimp (config := {etaStruct := .none, proj := true, iota := true}) only
  rw [hcp]
  dsimp (config := {etaStruct := .none, proj := true, iota := true}) only
  split
  next s1 i1 h1 =>
  obtain ⟨A1, g1, n1⟩ := jerk_arr h1 A0 hn' le_rfl (by norm_num) (hEs 0) (hEs 1)
  have A1' := A1.of_get (by rw [g1, hEs 2]; rfl)
  dsimp only at A1' n1
  split
  next s2 i2 h2 =>
  obtain ⟨A2, n2⟩ := const_arr h2 A1' n1 (by norm_num) (by norm_num) (hEs 3)
  dsimp only at A2 n2
  split
  next s3 i3 h3 =>
  obtain ⟨A3, g3, n3⟩ := jerk_arr h3 A2 n2 (by norm_num) (by norm_num) (hEs 4) (hEs 5)
  dsimp only at A3 g3 n3
  rw [show Int32.toNatClampNeg 7 = 7 from rfl, show Int32.toNatClampNeg 14 = 14 from rfl,
    show Int32.toNatClampNeg 22 = 22 from rfl]
  have A4 := setA_arr A3 (by norm_num) g3 (by rw [hEs 6]; rfl)
  rw [forIn7 _ _ zstep ?hf]
  case hf =>
    intro x b
    split
    next a c h => simp only [zstep, h]; rfl
  set X : SCurve.State :=
    { s3 with num_segs := i3, segment := s3.segment.set! 7 { s3.segment[7]! with end_accel := 0.0 } }
    with hX
  have B8 : Arr X.segment 8 E := A4
  have m8 : X.num_segs.toNat = 8 := n3
  obtain ⟨B9, m9⟩ := zstep_arr B8 m8 (by norm_num) (by norm_num) (hEs 7)
  obtain ⟨B10, m10⟩ := zstep_arr B9 m9 (by norm_num) (by norm_num) (hEs 8)
  obtain ⟨B11, m11⟩ := zstep_arr B10 m10 (by norm_num) (by norm_num) (hEs 9)
  obtain ⟨B12, m12⟩ := zstep_arr B11 m11 (by norm_num) (by norm_num) (hEs 10)
  obtain ⟨B13, m13⟩ := zstep_arr B12 m12 (by norm_num) (by norm_num) (hEs 11)
  obtain ⟨B14, m14⟩ := zstep_arr B13 m13 (by norm_num) (by norm_num) (hEs 12)
  obtain ⟨B15, m15⟩ := zstep_arr B14 m14 (by norm_num) (by norm_num) (hEs 13)
  generalize zstep (zstep (zstep (zstep (zstep (zstep (zstep X)))))) = Y at B15 m15 ⊢
  rw [id_bind_eq]
  split
  next s5 i5 h5 =>
  obtain ⟨A5, n5⟩ := const_arr h5 B15 m15 (by norm_num) (by norm_num)
    (by rw [hEs 14, B15.2 14 (by norm_num)]; rfl)
  dsimp only at A5 n5
  split
  next s6 i6 h6 =>
  obtain ⟨A6, g6, n6⟩ := jerk_arr h6 A5 n5 (by norm_num) (by norm_num) (hEs 15) (hEs 16)
  have A6' := A6.of_get (by rw [g6, hEs 17]; rfl)
  dsimp only at A6' n6
  split
  next s7 i7 h7 =>
  obtain ⟨A7, n7⟩ := const_arr h7 A6' n6 (by norm_num) (by norm_num) (hEs 18)
  dsimp only at A7 n7
  split
  next s8 i8 h8 =>
  obtain ⟨A8, g8, n8⟩ := jerk_arr h8 A7 n7 (by norm_num) (by norm_num) (hEs 19) (hEs 20)
  dsimp only at A8 g8 n8
  exact ⟨n8, setAV_arr A8 (by norm_num) g8 (by rw [hEs 21]; rfl)⟩

end Contracts.Mission.SCT
