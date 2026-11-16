import Contracts.MissionPrelude

/-!
# The S-curve over the reals

The closed forms of `SCurve::calc_javp_for_segment_*` and the node formulas of
`SCurve::add_segment_*` (`AP_Math/SCurve.cpp`), over the reals with `β = π / tj`:

* the three segment types (raised-cosine increasing jerk, raised-cosine decreasing jerk, constant
  jerk), with their derivatives (`hasDerivAt_*`): position' = velocity, velocity' = acceleration,
  acceleration' = jerk;
* the node values at the end of a segment (`incrNode`, `decrNode`, `constNode`) agree with the
  closed forms at the segment's duration;
* the accelerating phase of `add_segments` (jerk up, constant acceleration, jerk down) ends at
  acceleration `0`, velocity `A_m (R + t₄)` and position `A_m (R + t₄)(2R + t₄)/2`
  (`accelPhase_node`), with `A_m = J_m (t_j + t₂)` and `R = 2 t_j + t₂`;
* the decelerating phase brings it back to rest at `2 P₇ + V₇ t₁₅`.
-/

namespace Contracts.Mission.SC

open Real

noncomputable section

/-- A node of the S-curve: acceleration, velocity, position. -/
structure Node where
  a : ℝ
  v : ℝ
  p : ℝ

/-! ## Monotonicity from derivatives -/

open Set in
theorem monoOn_of_hasDeriv {f f' : ℝ → ℝ} {d : ℝ} (hf : ∀ t, HasDerivAt f (f' t) t)
    (h : ∀ t ∈ Icc 0 d, 0 ≤ f' t) : MonotoneOn f (Icc 0 d) :=
  monotoneOn_of_deriv_nonneg (convex_Icc 0 d)
    (fun x _ => (hf x).continuousAt.continuousWithinAt)
    (fun x _ => (hf x).differentiableAt.differentiableWithinAt)
    (fun x hx => by rw [(hf x).deriv]; exact h x (interior_subset hx))

open Set in
theorem antiOn_of_hasDeriv {f f' : ℝ → ℝ} {d : ℝ} (hf : ∀ t, HasDerivAt f (f' t) t)
    (h : ∀ t ∈ Icc 0 d, f' t ≤ 0) : AntitoneOn f (Icc 0 d) :=
  antitoneOn_of_deriv_nonpos (convex_Icc 0 d)
    (fun x _ => (hf x).continuousAt.continuousWithinAt)
    (fun x _ => (hf x).differentiableAt.differentiableWithinAt)
    (fun x hx => by rw [(hf x).deriv]; exact h x (interior_subset hx))

open Set in
/-- **One segment.** If the jerk has a constant sign on `[0, d]`, the acceleration is of one sign at
both ends and the velocity is nonnegative at both ends, then the velocity is nonnegative and the
position nondecreasing on `[0, d]`. -/
theorem seg_mono {A V P J : ℝ → ℝ} {d : ℝ} (hd : 0 ≤ d) (hA : ∀ t, HasDerivAt A (J t) t)
    (hV : ∀ t, HasDerivAt V (A t) t) (hP : ∀ t, HasDerivAt P (V t) t)
    (hJ : (∀ t ∈ Icc 0 d, 0 ≤ J t) ∨ (∀ t ∈ Icc 0 d, J t ≤ 0))
    (hAs : (0 ≤ A 0 ∧ 0 ≤ A d) ∨ (A 0 ≤ 0 ∧ A d ≤ 0)) (hV0 : 0 ≤ V 0) (hVd : 0 ≤ V d) :
    (∀ t ∈ Icc 0 d, 0 ≤ V t) ∧ MonotoneOn P (Icc 0 d) := by
  have h0 : (0 : ℝ) ∈ Icc 0 d := ⟨le_rfl, hd⟩
  have hd' : d ∈ Icc 0 d := ⟨hd, le_rfl⟩
  -- the acceleration keeps the sign of its ends
  have hAsign : (∀ t ∈ Icc 0 d, 0 ≤ A t) ∨ (∀ t ∈ Icc 0 d, A t ≤ 0) := by
    rcases hJ with hJ | hJ
    · have hm := monoOn_of_hasDeriv hA hJ
      rcases hAs with ⟨a0, ad⟩ | ⟨a0, ad⟩
      · exact Or.inl fun t ht => a0.trans (hm h0 ht ht.1)
      · exact Or.inr fun t ht => (hm ht hd' ht.2).trans ad
    · have hm := antiOn_of_hasDeriv hA hJ
      rcases hAs with ⟨a0, ad⟩ | ⟨a0, ad⟩
      · exact Or.inl fun t ht => ad.trans (hm ht hd' ht.2)
      · exact Or.inr fun t ht => (hm h0 ht ht.1).trans a0
  have hVnn : ∀ t ∈ Icc 0 d, 0 ≤ V t := by
    rcases hAsign with hAs | hAs
    · have hm := monoOn_of_hasDeriv hV hAs
      exact fun t ht => hV0.trans (hm h0 ht ht.1)
    · have hm := antiOn_of_hasDeriv hV hAs
      exact fun t ht => hVd.trans (hm ht hd' ht.2)
  exact ⟨hVnn, monoOn_of_hasDeriv hP hVnn⟩

/-! ## Constant jerk -/

def cJ (J0 : ℝ) (_t : ℝ) : ℝ := J0
def cA (n : Node) (J0 t : ℝ) : ℝ := n.a + J0 * t
def cV (n : Node) (J0 t : ℝ) : ℝ := n.v + n.a * t + J0 * t ^ 2 / 2
def cP (n : Node) (J0 t : ℝ) : ℝ := n.p + n.v * t + n.a * t ^ 2 / 2 + J0 * t ^ 3 / 6

def constNode (n : Node) (J0 T : ℝ) : Node := ⟨cA n J0 T, cV n J0 T, cP n J0 T⟩

theorem hasDerivAt_cP (n : Node) (J0 t : ℝ) : HasDerivAt (cP n J0) (cV n J0 t) t := by
  have := ((((hasDerivAt_id t).const_mul n.v).const_add n.p).add
    (((hasDerivAt_pow 2 t).const_mul (n.a / 2)))).add ((hasDerivAt_pow 3 t).const_mul (J0 / 6))
  convert this using 1
  · funext s; simp only [cP, Pi.add_apply, id_eq]; ring
  · simp only [cV]; push_cast; ring

theorem hasDerivAt_cV (n : Node) (J0 t : ℝ) : HasDerivAt (cV n J0) (cA n J0 t) t := by
  have := (((hasDerivAt_id t).const_mul n.a).const_add n.v).add
    ((hasDerivAt_pow 2 t).const_mul (J0 / 2))
  convert this using 1
  · funext s; simp only [cV, Pi.add_apply, id_eq]; ring
  · simp only [cA]; push_cast; ring

theorem hasDerivAt_cA (n : Node) (J0 t : ℝ) : HasDerivAt (cA n J0) J0 t := by
  have := ((hasDerivAt_id t).const_mul J0).const_add n.a
  convert this using 1
  · funext s; simp only [cA, id_eq]
  · ring

/-! ## Increasing jerk: `J(t) = (J_m/2)(1 - cos(b t))`, with `b = π / t_j` -/

def iJ (Jm b t : ℝ) : ℝ := Jm / 2 * (1 - cos (b * t))
def iA (n : Node) (Jm b t : ℝ) : ℝ := n.a + Jm / 2 * t - Jm / 2 / b * sin (b * t)
def iV (n : Node) (Jm b t : ℝ) : ℝ :=
  n.v + n.a * t + Jm / 2 / 2 * t ^ 2 + Jm / 2 / b ^ 2 * cos (b * t) - Jm / 2 / b ^ 2
def iP (n : Node) (Jm b t : ℝ) : ℝ :=
  n.p + n.v * t + n.a * t ^ 2 / 2 + (-(Jm / 2) / b ^ 2) * t + Jm / 2 * t ^ 3 / 6 +
    Jm / 2 / b ^ 3 * sin (b * t)

theorem hasDerivAt_iA (n : Node) (Jm b t : ℝ) (hb : b ≠ 0) :
    HasDerivAt (iA n Jm b) (iJ Jm b t) t := by
  have h1 := ((hasDerivAt_id t).const_mul (Jm / 2)).const_add n.a
  have h2 := ((((hasDerivAt_id t).const_mul b).sin).const_mul (Jm / 2 / b))
  have := h1.sub h2
  convert this using 1
  · funext s; simp only [iA, Pi.sub_apply, id_eq]
  · simp only [iJ, id_eq]; field_simp

theorem hasDerivAt_iV (n : Node) (Jm b t : ℝ) (hb : b ≠ 0) :
    HasDerivAt (iV n Jm b) (iA n Jm b t) t := by
  have h1 := (((hasDerivAt_id t).const_mul n.a).const_add n.v).add
    ((hasDerivAt_pow 2 t).const_mul (Jm / 2 / 2))
  have h2 := (((hasDerivAt_id t).const_mul b).cos).const_mul (Jm / 2 / b ^ 2)
  have := (h1.add h2).sub_const (Jm / 2 / b ^ 2)
  convert this using 1
  · funext s; simp only [iV, Pi.add_apply, id_eq]
  · simp only [iA, id_eq]; push_cast; field_simp; ring

theorem hasDerivAt_iP (n : Node) (Jm b t : ℝ) (hb : b ≠ 0) :
    HasDerivAt (iP n Jm b) (iV n Jm b t) t := by
  have h1 := ((((hasDerivAt_id t).const_mul n.v).const_add n.p).add
    ((hasDerivAt_pow 2 t).const_mul (n.a / 2))).add ((hasDerivAt_id t).const_mul (-(Jm / 2) / b ^ 2))
  have h2 := (hasDerivAt_pow 3 t).const_mul (Jm / 2 / 6)
  have h3 := (((hasDerivAt_id t).const_mul b).sin).const_mul (Jm / 2 / b ^ 3)
  have := (h1.add h2).add h3
  convert this using 1
  · funext s; simp only [iP, Pi.add_apply, id_eq]; ring
  · simp only [iV, id_eq]; push_cast; field_simp; ring

/-! ## Decreasing jerk: `J(t) = (J_m/2)(1 - cos(b (t + t_j)))` -/

/-- `AT`, `VT`, `PT` of the code: the increasing-jerk ramp's own contribution over `t_j`. -/
def rAT (Jm tj : ℝ) : ℝ := Jm / 2 * tj
def rVT (Jm b tj : ℝ) : ℝ := Jm / 2 * (tj ^ 2 / 2 - 2 / b ^ 2)
def rPT (Jm b tj : ℝ) : ℝ := Jm / 2 * (-(1 / b ^ 2) * tj + tj ^ 3 / 6)

def dJ (Jm b tj t : ℝ) : ℝ := Jm / 2 * (1 - cos (b * (t + tj)))
def dA (n : Node) (Jm b tj t : ℝ) : ℝ :=
  (n.a - rAT Jm tj) + Jm / 2 * (t + tj) - Jm / 2 / b * sin (b * (t + tj))
def dV (n : Node) (Jm b tj t : ℝ) : ℝ :=
  (n.v - rVT Jm b tj) + (n.a - rAT Jm tj) * t + Jm / 2 / 2 * (t + tj) ^ 2 +
    Jm / 2 / b ^ 2 * cos (b * (t + tj)) - Jm / 2 / b ^ 2
def dP (n : Node) (Jm b tj t : ℝ) : ℝ :=
  (n.p - rPT Jm b tj) + (n.v - rVT Jm b tj) * t + (n.a - rAT Jm tj) * t ^ 2 / 2 +
    (-(Jm / 2) / b ^ 2) * (t + tj) + Jm / 2 / 6 * (t + tj) ^ 3 + Jm / 2 / b ^ 3 * sin (b * (t + tj))

theorem hasDerivAt_dA (n : Node) (Jm b tj t : ℝ) (hb : b ≠ 0) :
    HasDerivAt (dA n Jm b tj) (dJ Jm b tj t) t := by
  have h1 := (((hasDerivAt_id t).add_const tj).const_mul (Jm / 2)).const_add (n.a - rAT Jm tj)
  have h2 := (((((hasDerivAt_id t).add_const tj).const_mul b).sin).const_mul (Jm / 2 / b))
  have := h1.sub h2
  convert this using 1
  · funext s; simp only [dA, Pi.sub_apply, id_eq]
  · simp only [dJ, id_eq]; field_simp

theorem hasDerivAt_dV (n : Node) (Jm b tj t : ℝ) (hb : b ≠ 0) :
    HasDerivAt (dV n Jm b tj) (dA n Jm b tj t) t := by
  have h1 := (((hasDerivAt_id t).const_mul (n.a - rAT Jm tj)).const_add (n.v - rVT Jm b tj)).add
    ((((hasDerivAt_id t).add_const tj).pow 2).const_mul (Jm / 2 / 2))
  have h2 := ((((hasDerivAt_id t).add_const tj).const_mul b).cos).const_mul (Jm / 2 / b ^ 2)
  have := (h1.add h2).sub_const (Jm / 2 / b ^ 2)
  convert this using 1
  · funext s; simp only [dV, Pi.add_apply, Pi.pow_apply, id_eq]
  · simp only [dA, id_eq]; push_cast; field_simp; ring

theorem hasDerivAt_dP (n : Node) (Jm b tj t : ℝ) (hb : b ≠ 0) :
    HasDerivAt (dP n Jm b tj) (dV n Jm b tj t) t := by
  have h1 := ((((hasDerivAt_id t).const_mul (n.v - rVT Jm b tj)).const_add (n.p - rPT Jm b tj)).add
    ((hasDerivAt_pow 2 t).const_mul ((n.a - rAT Jm tj) / 2))).add
    (((hasDerivAt_id t).add_const tj).const_mul (-(Jm / 2) / b ^ 2))
  have h2 := (((hasDerivAt_id t).add_const tj).pow 3).const_mul (Jm / 2 / 6)
  have h3 := ((((hasDerivAt_id t).add_const tj).const_mul b).sin).const_mul (Jm / 2 / b ^ 3)
  have := (h1.add h2).add h3
  convert this using 1
  · funext s; simp only [dP, Pi.add_apply, Pi.pow_apply, id_eq]; ring
  · simp only [dV, id_eq]; push_cast; field_simp; ring

/-! ## Nodes (`add_segment_*`) -/

/-- `add_segment_incr_jerk`: the node after an increasing-jerk ramp of duration `t_j`. -/
def incrNode (n : Node) (Jm b tj : ℝ) : Node :=
  ⟨n.a + rAT Jm tj, n.v + n.a * tj + rVT Jm b tj, n.p + n.v * tj + n.a * tj ^ 2 / 2 + rPT Jm b tj⟩

/-- `P2T` of `add_segment_decr_jerk`. -/
def rP2T (Jm b tj : ℝ) : ℝ := Jm / 2 * (-(1 / b ^ 2) * 2 * tj + 4 / 3 * tj ^ 3)

/-- `add_segment_decr_jerk`: the node after a decreasing-jerk ramp of duration `t_j`. -/
def decrNode (n : Node) (Jm b tj : ℝ) : Node :=
  ⟨(n.a - rAT Jm tj) + Jm * tj, (n.v - rVT Jm b tj) + (n.a - rAT Jm tj) * tj + Jm * tj ^ 2,
    (n.p - rPT Jm b tj) + (n.v - rVT Jm b tj) * tj + (n.a - rAT Jm tj) * tj ^ 2 / 2 + rP2T Jm b tj⟩

/-- `add_segments_jerk`: increasing ramp, constant jerk for `T`, decreasing ramp. -/
def jerkNode (n : Node) (Jm b tj T : ℝ) : Node :=
  decrNode (constNode (incrNode n Jm b tj) Jm T) Jm b tj

/-- The node at the end of the accelerating phase of `add_segments` (segments 1–7), from rest. -/
def accelNode (Jm b tj t2 t4 t6 : ℝ) : Node :=
  jerkNode (constNode (jerkNode ⟨0, 0, 0⟩ Jm b tj t2) 0 t4) (-Jm) b tj t6

/-- **The accelerating phase** (with `t₆ = t₂`, as `calculate_path` always returns): it ends at
acceleration `0`, velocity `A_m (R + t₄)`, position `A_m (R + t₄)(2R + t₄)/2`, where
`A_m = J_m (t_j + t₂)` and `R = 2 t_j + t₂`. For every `b ≠ 0`: the `1/b²` terms cancel. -/
theorem accelNode_eq (Jm b tj t2 t4 : ℝ) (hb : b ≠ 0) :
    accelNode Jm b tj t2 t4 t2 =
      ⟨0, Jm * (tj + t2) * (2 * tj + t2 + t4),
        Jm * (tj + t2) * (2 * tj + t2 + t4) * (2 * (2 * tj + t2) + t4) / 2⟩ := by
  simp only [accelNode, jerkNode, decrNode, constNode, incrNode, cA, cV, cP, rAT, rVT, rPT, rP2T]
  congr 1 <;> field_simp <;> ring

/-- The node at the end of the decelerating phase (segments 15–22), from a node at rest in
acceleration with velocity `V` and position `P`: constant velocity for `t₁₅`, then the mirror of
the accelerating phase. -/
def decelNode (n : Node) (Jm b tj t2 t4 t6 t15 : ℝ) : Node :=
  jerkNode (constNode (jerkNode (constNode n 0 t15) (-Jm) b tj t6) 0 t4) Jm b tj t2

/-- **The decelerating phase** brings the accelerating phase's end node back to rest at
`2 P₇ + V₇ t₁₅`. -/
theorem decelNode_eq (Jm b tj t2 t4 t15 : ℝ) (hb : b ≠ 0) :
    decelNode (accelNode Jm b tj t2 t4 t2) Jm b tj t2 t4 t2 t15 =
      ⟨0, 0, 2 * (accelNode Jm b tj t2 t4 t2).p + (accelNode Jm b tj t2 t4 t2).v * t15⟩ := by
  rw [accelNode_eq Jm b tj t2 t4 hb]
  simp only [decelNode, jerkNode, decrNode, constNode, incrNode, cA, cV, cP, rAT, rVT, rPT, rP2T]
  congr 1 <;> field_simp <;> ring

/-! ## Segments -/

/-- The three segment types of `SCurve` (`SegmentType`). -/
inductive Kind where
  | const
  | incr
  | decr

/-- A segment: its type, its jerk parameter (`J0` or `J_m`), its duration. -/
structure Seg where
  kind : Kind
  J : ℝ
  d : ℝ

/-- The closed forms of a segment from node `n` (with `b = π / d` for the ramps). -/
def Seg.jerk (s : Seg) : ℝ → ℝ :=
  match s.kind with
  | .const => cJ s.J
  | .incr => iJ s.J (π / s.d)
  | .decr => dJ s.J (π / s.d) s.d
def Seg.acc (s : Seg) (n : Node) : ℝ → ℝ :=
  match s.kind with
  | .const => cA n s.J
  | .incr => iA n s.J (π / s.d)
  | .decr => dA n s.J (π / s.d) s.d
def Seg.vel (s : Seg) (n : Node) : ℝ → ℝ :=
  match s.kind with
  | .const => cV n s.J
  | .incr => iV n s.J (π / s.d)
  | .decr => dV n s.J (π / s.d) s.d
def Seg.pos (s : Seg) (n : Node) : ℝ → ℝ :=
  match s.kind with
  | .const => cP n s.J
  | .incr => iP n s.J (π / s.d)
  | .decr => dP n s.J (π / s.d) s.d

/-- The node at the end of a segment. -/
def Seg.node (s : Seg) (n : Node) : Node :=
  match s.kind with
  | .const => constNode n s.J s.d
  | .incr => incrNode n s.J (π / s.d) s.d
  | .decr => decrNode n s.J (π / s.d) s.d

theorem Seg.hasDerivAt_acc (s : Seg) (n : Node) (hd : 0 < s.d) (t : ℝ) :
    HasDerivAt (s.acc n) (s.jerk t) t := by
  have hb : π / s.d ≠ 0 := div_ne_zero pi_ne_zero hd.ne'
  cases h : s.kind <;> simp only [Seg.acc, Seg.jerk, h]
  · exact hasDerivAt_cA n s.J t
  · exact hasDerivAt_iA n s.J _ t hb
  · exact hasDerivAt_dA n s.J _ s.d t hb

theorem Seg.hasDerivAt_vel (s : Seg) (n : Node) (hd : 0 < s.d) (t : ℝ) :
    HasDerivAt (s.vel n) (s.acc n t) t := by
  have hb : π / s.d ≠ 0 := div_ne_zero pi_ne_zero hd.ne'
  cases h : s.kind <;> simp only [Seg.acc, Seg.vel, h]
  · exact hasDerivAt_cV n s.J t
  · exact hasDerivAt_iV n s.J _ t hb
  · exact hasDerivAt_dV n s.J _ s.d t hb

theorem Seg.hasDerivAt_pos (s : Seg) (n : Node) (hd : 0 < s.d) (t : ℝ) :
    HasDerivAt (s.pos n) (s.vel n t) t := by
  have hb : π / s.d ≠ 0 := div_ne_zero pi_ne_zero hd.ne'
  cases h : s.kind <;> simp only [Seg.pos, Seg.vel, h]
  · exact hasDerivAt_cP n s.J t
  · exact hasDerivAt_iP n s.J _ t hb
  · exact hasDerivAt_dP n s.J _ s.d t hb

/-- The jerk of a segment has the sign of its parameter. -/
theorem Seg.jerk_sign (s : Seg) (t : ℝ) : (0 ≤ s.J → 0 ≤ s.jerk t) ∧ (s.J ≤ 0 → s.jerk t ≤ 0) := by
  have h1 : 0 ≤ 1 - cos (π / s.d * t) := by linarith [cos_le_one (π / s.d * t)]
  have h2 : 0 ≤ 1 - cos (π / s.d * (t + s.d)) := by linarith [cos_le_one (π / s.d * (t + s.d))]
  cases h : s.kind <;> simp only [Seg.jerk, h, cJ, iJ, dJ]
  · exact ⟨id, id⟩
  · exact ⟨fun hJ => mul_nonneg (by linarith) h1, fun hJ => mul_nonpos_of_nonpos_of_nonneg (by linarith) h1⟩
  · exact ⟨fun hJ => mul_nonneg (by linarith) h2, fun hJ => mul_nonpos_of_nonpos_of_nonneg (by linarith) h2⟩

/-- At its start a segment is at its start node. -/
theorem Seg.at_zero (s : Seg) (n : Node) (hd : 0 < s.d) :
    s.acc n 0 = n.a ∧ s.vel n 0 = n.v ∧ s.pos n 0 = n.p := by
  have hb : π / s.d * s.d = π := div_mul_cancel₀ _ hd.ne'
  cases h : s.kind <;> simp only [Seg.acc, Seg.vel, Seg.pos, h]
  · simp [cA, cV, cP]
  · simp [iA, iV, iP]
  · simp only [dA, dV, dP, zero_add, rAT, rVT, rPT, hb, sin_pi, cos_pi]
    refine ⟨by ring, by field_simp; ring, by field_simp; ring⟩

/-- At its end a segment is at its end node. -/
theorem Seg.at_end (s : Seg) (n : Node) (hd : 0 < s.d) :
    s.acc n s.d = (s.node n).a ∧ s.vel n s.d = (s.node n).v ∧ s.pos n s.d = (s.node n).p := by
  have hb : π / s.d * s.d = π := div_mul_cancel₀ _ hd.ne'
  have hb2 : π / s.d * (s.d + s.d) = 2 * π := by rw [mul_add, hb]; ring
  cases h : s.kind <;> simp only [Seg.acc, Seg.vel, Seg.pos, Seg.node, h]
  · simp [cA, cV, cP, constNode]
  · simp only [iA, iV, iP, incrNode, hb, sin_pi, cos_pi, rAT, rVT, rPT]
    refine ⟨by ring, by field_simp; ring, by field_simp; ring⟩
  · simp only [dA, dV, dP, decrNode, hb2, sin_two_pi, cos_two_pi, rAT, rVT, rPT, rP2T]
    refine ⟨by ring, by field_simp; ring, by field_simp; ring⟩

/-! ## Signs along a segment -/

open Set

/-- Duration-zero constant segments and positive-duration segments: the closed forms have the
derivatives of `Seg.hasDerivAt_*`. -/
def Seg.Ok (s : Seg) : Prop := (s.kind = .const ∧ 0 ≤ s.d) ∨ 0 < s.d

theorem Seg.Ok.d_nonneg {s : Seg} (h : s.Ok) : 0 ≤ s.d := by
  rcases h with ⟨-, h⟩ | h
  · exact h
  · exact h.le

theorem Seg.deriv_acc {s : Seg} (h : s.Ok) (n : Node) (t : ℝ) :
    HasDerivAt (s.acc n) (s.jerk t) t := by
  rcases h with ⟨hk, -⟩ | h
  · simp only [Seg.acc, Seg.jerk, hk]; exact hasDerivAt_cA n s.J t
  · exact s.hasDerivAt_acc n h t

theorem Seg.deriv_vel {s : Seg} (h : s.Ok) (n : Node) (t : ℝ) :
    HasDerivAt (s.vel n) (s.acc n t) t := by
  rcases h with ⟨hk, -⟩ | h
  · simp only [Seg.acc, Seg.vel, hk]; exact hasDerivAt_cV n s.J t
  · exact s.hasDerivAt_vel n h t

theorem Seg.deriv_pos {s : Seg} (h : s.Ok) (n : Node) (t : ℝ) :
    HasDerivAt (s.pos n) (s.vel n t) t := by
  rcases h with ⟨hk, -⟩ | h
  · simp only [Seg.pos, Seg.vel, hk]; exact hasDerivAt_cP n s.J t
  · exact s.hasDerivAt_pos n h t

theorem Seg.ends {s : Seg} (h : s.Ok) (n : Node) :
    (s.acc n 0 = n.a ∧ s.vel n 0 = n.v ∧ s.pos n 0 = n.p) ∧
      (s.acc n s.d = (s.node n).a ∧ s.vel n s.d = (s.node n).v ∧ s.pos n s.d = (s.node n).p) := by
  rcases h with ⟨hk, -⟩ | h
  · simp only [Seg.acc, Seg.vel, Seg.pos, Seg.node, hk]
    simp [cA, cV, cP, constNode]
  · exact ⟨s.at_zero n h, s.at_end n h⟩

/-- A segment whose acceleration is nonnegative at both ends, with jerk of one sign, has a
nonnegative acceleration and a nondecreasing velocity throughout. -/
theorem Seg.acc_nonneg {s : Seg} (h : s.Ok) (n : Node) (hJ : 0 ≤ s.J ∨ s.J ≤ 0)
    (ha0 : 0 ≤ n.a) (had : 0 ≤ (s.node n).a) :
    (∀ t ∈ Icc 0 s.d, 0 ≤ s.acc n t) ∧ n.v ≤ (s.node n).v := by
  obtain ⟨⟨e0, v0, -⟩, ⟨ed, vd, -⟩⟩ := s.ends h n
  have h0 : (0 : ℝ) ∈ Icc 0 s.d := ⟨le_rfl, h.d_nonneg⟩
  have hd : s.d ∈ Icc 0 s.d := ⟨h.d_nonneg, le_rfl⟩
  have hA : ∀ t ∈ Icc 0 s.d, 0 ≤ s.acc n t := by
    rcases hJ with hJ | hJ
    · have hm := monoOn_of_hasDeriv (d := s.d) (s.deriv_acc h n) (fun t _ => (s.jerk_sign t).1 hJ)
      exact fun t ht => (e0 ▸ ha0).trans (hm h0 ht ht.1)
    · have hm := antiOn_of_hasDeriv (d := s.d) (s.deriv_acc h n) (fun t _ => (s.jerk_sign t).2 hJ)
      exact fun t ht => (ed ▸ had).trans (hm ht hd ht.2)
  refine ⟨hA, ?_⟩
  have hm := monoOn_of_hasDeriv (s.deriv_vel h n) hA
  rw [← v0, ← vd]; exact hm h0 hd h.d_nonneg

/-- The mirror: nonpositive acceleration, nonincreasing velocity. -/
theorem Seg.acc_nonpos {s : Seg} (h : s.Ok) (n : Node) (hJ : 0 ≤ s.J ∨ s.J ≤ 0)
    (ha0 : n.a ≤ 0) (had : (s.node n).a ≤ 0) :
    (∀ t ∈ Icc 0 s.d, s.acc n t ≤ 0) ∧ (s.node n).v ≤ n.v := by
  obtain ⟨⟨e0, v0, -⟩, ⟨ed, vd, -⟩⟩ := s.ends h n
  have h0 : (0 : ℝ) ∈ Icc 0 s.d := ⟨le_rfl, h.d_nonneg⟩
  have hd : s.d ∈ Icc 0 s.d := ⟨h.d_nonneg, le_rfl⟩
  have hA : ∀ t ∈ Icc 0 s.d, s.acc n t ≤ 0 := by
    rcases hJ with hJ | hJ
    · have hm := monoOn_of_hasDeriv (d := s.d) (s.deriv_acc h n) (fun t _ => (s.jerk_sign t).1 hJ)
      exact fun t ht => (hm ht hd ht.2).trans (ed ▸ had)
    · have hm := antiOn_of_hasDeriv (d := s.d) (s.deriv_acc h n) (fun t _ => (s.jerk_sign t).2 hJ)
      exact fun t ht => (hm h0 ht ht.1).trans (e0 ▸ ha0)
  refine ⟨hA, ?_⟩
  have hm := antiOn_of_hasDeriv (s.deriv_vel h n) hA
  rw [← v0, ← vd]; exact hm h0 hd h.d_nonneg

/-- With a signed acceleration and nonnegative velocity at both ends, the velocity is nonnegative
and the position nondecreasing throughout. -/
theorem Seg.pos_mono {s : Seg} (h : s.Ok) (n : Node)
    (hA : (∀ t ∈ Icc 0 s.d, 0 ≤ s.acc n t) ∨ (∀ t ∈ Icc 0 s.d, s.acc n t ≤ 0))
    (hv0 : 0 ≤ n.v) (hvd : 0 ≤ (s.node n).v) :
    (∀ t ∈ Icc 0 s.d, 0 ≤ s.vel n t) ∧ MonotoneOn (s.pos n) (Icc 0 s.d) := by
  obtain ⟨⟨-, v0, -⟩, ⟨-, vd, -⟩⟩ := s.ends h n
  have h0 : (0 : ℝ) ∈ Icc 0 s.d := ⟨le_rfl, h.d_nonneg⟩
  have hd : s.d ∈ Icc 0 s.d := ⟨h.d_nonneg, le_rfl⟩
  have hV : ∀ t ∈ Icc 0 s.d, 0 ≤ s.vel n t := by
    rcases hA with hA | hA
    · have hm := monoOn_of_hasDeriv (s.deriv_vel h n) hA
      exact fun t ht => (v0 ▸ hv0).trans (hm h0 ht ht.1)
    · have hm := antiOn_of_hasDeriv (s.deriv_vel h n) hA
      exact fun t ht => (vd ▸ hvd).trans (hm ht hd ht.2)
  exact ⟨hV, monoOn_of_hasDeriv (s.deriv_pos h n) hV⟩

/-! ## The profile of `add_segments` -/

@[simp] theorem constNode_a (n : Node) (J T : ℝ) : (constNode n J T).a = n.a + J * T := rfl
@[simp] theorem incrNode_a (n : Node) (J b T : ℝ) : (incrNode n J b T).a = n.a + rAT J T := rfl
@[simp] theorem decrNode_a (n : Node) (J b T : ℝ) :
    (decrNode n J b T).a = (n.a - rAT J T) + J * T := rfl
@[simp] theorem constNode_v (n : Node) (J T : ℝ) :
    (constNode n J T).v = n.v + n.a * T + J * T ^ 2 / 2 := rfl

/-- The segments of `SCurve::add_segments` (code segments `1 … 22`; segment `0` is the start node):
the accelerating phase `1–7`, seven empty segments `8–14`, constant velocity `15`, the decelerating
phase `16–22`. -/
def prof (Jm tj t2 t4 t15 : ℝ) : ℕ → Seg
  | 0 => ⟨.incr, Jm, tj⟩
  | 1 => ⟨.const, Jm, t2⟩
  | 2 => ⟨.decr, Jm, tj⟩
  | 3 => ⟨.const, 0, t4⟩
  | 4 => ⟨.incr, -Jm, tj⟩
  | 5 => ⟨.const, -Jm, t2⟩
  | 6 => ⟨.decr, -Jm, tj⟩
  | 14 => ⟨.const, 0, t15⟩
  | 15 => ⟨.incr, -Jm, tj⟩
  | 16 => ⟨.const, -Jm, t2⟩
  | 17 => ⟨.decr, -Jm, tj⟩
  | 18 => ⟨.const, 0, t4⟩
  | 19 => ⟨.incr, Jm, tj⟩
  | 20 => ⟨.const, Jm, t2⟩
  | 21 => ⟨.decr, Jm, tj⟩
  | _ => ⟨.const, 0, 0⟩

/-- The nodes of the profile: `node k` is the end node of code segment `k`. -/
def node (Jm tj t2 t4 t15 : ℝ) : ℕ → Node
  | 0 => ⟨0, 0, 0⟩
  | k + 1 => (prof Jm tj t2 t4 t15 k).node (node Jm tj t2 t4 t15 k)

section Profile

variable {Jm tj t2 t4 t15 : ℝ}

theorem prof_ok (htj : 0 < tj) (h2 : 0 ≤ t2) (h4 : 0 ≤ t4) (h15 : 0 ≤ t15) (k : ℕ) :
    (prof Jm tj t2 t4 t15 k).Ok := by
  unfold prof Seg.Ok
  rcases k with _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | _ | k
  all_goals first | exact Or.inr htj | exact Or.inl ⟨rfl, by assumption⟩ | exact Or.inl ⟨rfl, le_rfl⟩

/-- The accelerations at the nodes. -/
theorem node_a :
    (node Jm tj t2 t4 t15 1).a = Jm * tj / 2 ∧
    (node Jm tj t2 t4 t15 2).a = Jm * tj / 2 + Jm * t2 ∧
    (node Jm tj t2 t4 t15 3).a = Jm * (tj + t2) ∧
    (node Jm tj t2 t4 t15 4).a = Jm * (tj + t2) ∧
    (node Jm tj t2 t4 t15 5).a = Jm * tj / 2 + Jm * t2 ∧
    (node Jm tj t2 t4 t15 6).a = Jm * tj / 2 ∧
    (node Jm tj t2 t4 t15 7).a = 0 ∧
    (node Jm tj t2 t4 t15 14).a = 0 ∧
    (node Jm tj t2 t4 t15 15).a = 0 ∧
    (node Jm tj t2 t4 t15 16).a = -(Jm * tj / 2) ∧
    (node Jm tj t2 t4 t15 17).a = -(Jm * tj / 2 + Jm * t2) ∧
    (node Jm tj t2 t4 t15 18).a = -(Jm * (tj + t2)) ∧
    (node Jm tj t2 t4 t15 19).a = -(Jm * (tj + t2)) ∧
    (node Jm tj t2 t4 t15 20).a = -(Jm * tj / 2 + Jm * t2) ∧
    (node Jm tj t2 t4 t15 21).a = -(Jm * tj / 2) ∧
    (node Jm tj t2 t4 t15 22).a = 0 := by
  simp only [node, prof, Seg.node, constNode_a, incrNode_a, decrNode_a, rAT]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> ring

theorem constNode_zero (n : Node) : constNode n 0 0 = n := by
  cases n; simp [constNode, cA, cV, cP]

/-- The end of the accelerating phase is `accelNode`. -/
theorem node_7 : node Jm tj t2 t4 t15 7 = accelNode Jm (π / tj) tj t2 t4 t2 := rfl

theorem node_14 : node Jm tj t2 t4 t15 14 = node Jm tj t2 t4 t15 7 := by
  simp only [node, prof, Seg.node, constNode_zero]

/-- The end of the profile is `decelNode` of the end of the accelerating phase. -/
theorem node_22 :
    node Jm tj t2 t4 t15 22 = decelNode (node Jm tj t2 t4 t15 7) Jm (π / tj) tj t2 t4 t2 t15 := by
  rw [← node_14 (t15 := t15)]
  rfl

/-- **The profile's end**: at rest at `2 P₇ + V₇ t₁₅`. -/
theorem node_22_eq (htj : 0 < tj) :
    node Jm tj t2 t4 t15 22 = ⟨0, 0, 2 * (node Jm tj t2 t4 t15 7).p + (node Jm tj t2 t4 t15 7).v * t15⟩ := by
  rw [node_22, node_7]
  exact decelNode_eq Jm _ tj t2 t4 t15 (div_ne_zero pi_ne_zero htj.ne')

/-- **The profile's accelerating phase**: `P₇ = A_m (R + t₄)(2R + t₄)/2`, `V₇ = A_m (R + t₄)`. -/
theorem node_7_eq (htj : 0 < tj) :
    node Jm tj t2 t4 t15 7 = ⟨0, Jm * (tj + t2) * (2 * tj + t2 + t4),
      Jm * (tj + t2) * (2 * tj + t2 + t4) * (2 * (2 * tj + t2) + t4) / 2⟩ := by
  rw [node_7]; exact accelNode_eq Jm _ tj t2 t4 (div_ne_zero pi_ne_zero htj.ne')

/-- **The profile is monotone**: every node velocity is nonnegative, and on every segment the
velocity is nonnegative and the position nondecreasing. -/
theorem prof_mono (hJm : 0 ≤ Jm) (htj : 0 < tj) (h2 : 0 ≤ t2) (h4 : 0 ≤ t4) (h15 : 0 ≤ t15) :
    (∀ k ≤ 22, 0 ≤ (node Jm tj t2 t4 t15 k).v) ∧
    ∀ k < 22, (∀ t ∈ Set.Icc 0 (prof Jm tj t2 t4 t15 k).d,
        0 ≤ (prof Jm tj t2 t4 t15 k).vel (node Jm tj t2 t4 t15 k) t) ∧
      MonotoneOn ((prof Jm tj t2 t4 t15 k).pos (node Jm tj t2 t4 t15 k))
        (Set.Icc 0 (prof Jm tj t2 t4 t15 k).d) := by
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
  -- the empty segments `8 … 14` keep the node
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
  -- velocities: up through the accelerating phase
  have up : ∀ k, k < 7 → (N k).v ≤ (N (k + 1)).v ∧ ∀ t ∈ Set.Icc 0 (S k).d, 0 ≤ (S k).acc (N k) t := by
    intro k hk
    have hA0 : 0 ≤ (N k).a := by interval_cases k <;> simp only [a0, a1, a2, a3, a4, a5, a6] <;> positivity
    have hAd : 0 ≤ (N (k + 1)).a := by
      interval_cases k <;> simp only [a1, a2, a3, a4, a5, a6, a7, zero_add] <;> positivity
    rw [hNs] at hAd ⊢
    exact ⟨(Seg.acc_nonneg (ok k) _ (hJs k) hA0 hAd).2, (Seg.acc_nonneg (ok k) _ (hJs k) hA0 hAd).1⟩
  -- and down through the decelerating phase
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
  -- the node velocities
  have v15 : (N 15).v = (N 14).v := by
    rw [hNs]; simp only [hS, prof, Seg.node, constNode_v, a14]; ring
  have v22 : (N 22).v = 0 := by rw [hN, node_22_eq htj]
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
  have hv : ∀ k ≤ 22, 0 ≤ (N k).v := by
    intro k hk
    interval_cases k
    all_goals first
      | (simp only [v0]; exact le_rfl)
      | (simp only [e8, e9, e10, e11, e12, e13, e14, v15]; linarith)
      | linarith
  refine ⟨hv, fun k hk => ?_⟩
  have hvk := hv k hk.le
  have hvk1 := hv (k + 1) hk
  rw [hNs] at hvk1
  refine Seg.pos_mono (ok k) (N k) ?_ hvk hvk1
  by_cases h7 : k < 7
  · exact Or.inl (up k h7).2
  by_cases h15 : 15 ≤ k
  · exact Or.inr (dn k h15 hk).2
  -- the empty segments and constant velocity: zero acceleration
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

end Profile

end

end Contracts.Mission.SC
