import Contracts.Mission.SCurveTableFloat
import Contracts.Mission.SCurveProfile

/-!
# Entries of the `add_segments` table near the real nodes

`Near e t n eT eA eV eP`: the entry `e` ends within `eT` of time `t` and within `eA`, `eV`, `eP` of
the node `n`. One step of the table (`near_incr`, `near_decr`, `near_const`, …) carries `Near`
from an entry to the next: the rounding of the step (`SCurveTableFloat.lean`) plus the propagation
of the previous errors, which is linear (`lin_*`).
-/

namespace Contracts.Mission

open Float.Model UnpackedFloat AC_WPNav_lib

noncomputable section

namespace SCT

/-- The entry `e` ends within `eT` of `t` and within `eA`, `eV`, `eP` of the node `n`. -/
def Near (e : SCurve.segment_t) (t : ℝ) (n : SC.Node) (eT eA eV eP : ℝ) : Prop :=
  A32 e.end_time t eT ∧ A32 e.end_accel n.a eA ∧ A32 e.end_vel n.v eV ∧ A32 e.end_pos n.p eP

theorem Near.mono {e : SCurve.segment_t} {t : ℝ} {n : SC.Node} {eT eA eV eP eT' eA' eV' eP' : ℝ}
    (h : Near e t n eT eA eV eP) (h1 : eT ≤ eT') (h2 : eA ≤ eA') (h3 : eV ≤ eV') (h4 : eP ≤ eP') :
    Near e t n eT' eA' eV' eP' :=
  ⟨h.1.mono h1, h.2.1.mono h2, h.2.2.1.mono h3, h.2.2.2.mono h4⟩

/-- The float node of an entry. -/
def fnode (e : SCurve.segment_t) : SC.Node := ⟨e.end_accel.toReal, e.end_vel.toReal, e.end_pos.toReal⟩

/-- Steps whose node map is affine in the start node with the structure of a segment of
duration `d`. -/
def Lin (X : SC.Node → SC.Node) (d : ℝ) : Prop :=
  ∀ m m' : SC.Node, (X m').a - (X m).a = m'.a - m.a ∧
    (X m').v - (X m).v = (m'.v - m.v) + (m'.a - m.a) * d ∧
    (X m').p - (X m).p = (m'.p - m.p) + (m'.v - m.v) * d + (m'.a - m.a) * (d ^ 2 / 2)

theorem lin_const (J d : ℝ) : Lin (fun m => SC.constNode m J d) d := fun m m' => by
  simp only [SC.constNode, SC.cA, SC.cV, SC.cP]; refine ⟨by ring, by ring, by ring⟩

theorem lin_incr (J b d : ℝ) : Lin (fun m => SC.incrNode m J b d) d := fun m m' => by
  simp only [SC.incrNode]; refine ⟨by ring, by ring, by ring⟩

theorem lin_decr (J b d : ℝ) : Lin (fun m => SC.decrNode m J b d) d := fun m m' => by
  simp only [SC.decrNode]; refine ⟨by ring, by ring, by ring⟩

/-- **One step**: the rounding `cA`, `cV`, `cP` of the step on the float node of `p`, plus the
propagation of the errors of `p`. -/
theorem near_of_float {e p : SCurve.segment_t} {t t' d D cA cV cP eT eA eV eP eT' : ℝ}
    {n : SC.Node} {X : SC.Node → SC.Node} (hp : Near p t n eT eA eV eP) (hX : Lin X d)
    (hd0 : 0 ≤ d) (hdD : d ≤ D) (hT : A32 e.end_time t' eT')
    (hF : A32 e.end_accel (X (fnode p)).a cA ∧ A32 e.end_vel (X (fnode p)).v cV ∧
      A32 e.end_pos (X (fnode p)).p cP) :
    Near e t' (X n) eT' (eA + cA) (eV + D * eA + cV) (eP + D * eV + D ^ 2 / 2 * eA + cP) := by
  obtain ⟨-, ⟨-, ha⟩, ⟨-, hv⟩, ⟨-, hpp⟩⟩ := hp
  obtain ⟨⟨fa, ha'⟩, ⟨fv, hv'⟩, ⟨fp, hp'⟩⟩ := hF
  obtain ⟨la, lv, lp⟩ := hX n (fnode p)
  simp only [fnode] at la lv lp ha' hv' hp'
  have hea := (abs_nonneg _).trans ha
  have hev := (abs_nonneg _).trans hv
  have hd2 : d ^ 2 / 2 ≤ D ^ 2 / 2 := by
    have : d ^ 2 ≤ D ^ 2 := pow_le_pow_left₀ hd0 hdD 2
    linarith
  have hd2' : 0 ≤ d ^ 2 / 2 := by positivity
  refine ⟨hT, ⟨fa, ?_⟩, ⟨fv, ?_⟩, ⟨fp, ?_⟩⟩
  · have := abs_sub_le e.end_accel.toReal (X ⟨p.end_accel.toReal, p.end_vel.toReal,
      p.end_pos.toReal⟩).a (X n).a
    rw [la] at this; linarith
  · have h1 := abs_sub_le e.end_vel.toReal (X ⟨p.end_accel.toReal, p.end_vel.toReal,
      p.end_pos.toReal⟩).v (X n).v
    rw [lv] at h1
    have h2 := abs_add_le (p.end_vel.toReal - n.v) ((p.end_accel.toReal - n.a) * d)
    rw [abs_mul, abs_of_nonneg hd0] at h2
    have h3 : |p.end_accel.toReal - n.a| * d ≤ eA * D := mul_le_mul ha hdD hd0 hea
    linarith
  · have h1 := abs_sub_le e.end_pos.toReal (X ⟨p.end_accel.toReal, p.end_vel.toReal,
      p.end_pos.toReal⟩).p (X n).p
    rw [lp] at h1
    have h2 := abs_add_le ((p.end_pos.toReal - n.p) + (p.end_vel.toReal - n.v) * d)
      ((p.end_accel.toReal - n.a) * (d ^ 2 / 2))
    have h2' := abs_add_le (p.end_pos.toReal - n.p) ((p.end_vel.toReal - n.v) * d)
    rw [abs_mul, abs_of_nonneg hd2'] at h2
    rw [abs_mul, abs_of_nonneg hd0] at h2'
    have h3 : |p.end_vel.toReal - n.v| * d ≤ eV * D := mul_le_mul hv hdD hd0 hev
    have h4 : |p.end_accel.toReal - n.a| * (d ^ 2 / 2) ≤ eA * (D ^ 2 / 2) :=
      mul_le_mul ha hd2 hd2' hea
    linarith

/-- The end time of a step: `T₀ + d` rounded. -/
theorem near_time {T0 tin : Float32} {t TM eT : ℝ} (h : A32 T0 t eT) (ft : tin.IsFinite)
    (hTM : |t + tin.toReal| ≤ TM) (hcap : TM ≤ 2 ^ 20) (heT : eT ≤ 1) :
    A32 (T0 + tin) (t + tin.toReal) (eT + (TM + eT) / 16777216 + 1 / 10 ^ 40) := by
  have hT0 : 0 ≤ eT := (abs_nonneg _).trans h.2
  refine A32.add_c h (A32.of_exact ft) hTM (by norm_num [capF]; linarith) ?_
  linarith

/-- The magnitudes of the float node from the real node and the errors. -/
theorem near_mag {p : SCurve.segment_t} {t : ℝ} {n : SC.Node} {eT eA eV eP AM VM PM : ℝ}
    (hp : Near p t n eT eA eV eP) (hA : |n.a| + eA ≤ AM) (hV : |n.v| + eV ≤ VM)
    (hP : |n.p| + eP ≤ PM) :
    |p.end_accel.toReal| ≤ AM ∧ |p.end_vel.toReal| ≤ VM ∧ |p.end_pos.toReal| ≤ PM := by
  have a := hp.2.1.abs_le
  have v := hp.2.2.1.abs_le
  have q := hp.2.2.2.abs_le
  exact ⟨by linarith, by linarith, by linarith⟩

theorem Near.fin {p : SCurve.segment_t} {t : ℝ} {n : SC.Node} {eT eA eV eP : ℝ}
    (hp : Near p t n eT eA eV eP) :
    p.end_time.IsFinite ∧ p.end_accel.IsFinite ∧ p.end_vel.IsFinite ∧ p.end_pos.IsFinite :=
  ⟨hp.1.1, hp.2.1.1, hp.2.2.1.1, hp.2.2.2.1⟩

/-! ## The entries -/

theorem incrE_pos {p : SCurve.segment_t} {tj Jm : Float32} (h : is_positive_float tj = true) :
    (incrE p tj Jm).end_time = p.end_time + tj ∧
    (incrE p tj Jm).end_accel = p.end_accel + Jm * (0.5 : Float32) * tj ∧
    (incrE p tj Jm).end_vel = p.end_vel + p.end_accel * tj + vtF tj Jm ∧
    (incrE p tj Jm).end_pos = p.end_pos + p.end_vel * tj + (0.5 : Float32) * p.end_accel *
      sq_float tj + ptF tj Jm ∧
    (incrE p tj Jm).seg_type = .POSITIVE_JERK ∧ (incrE p tj Jm).jerk_ref = Jm := by
  rw [incrE, ite_eq_left h]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem decrE_pos {p : SCurve.segment_t} {tj Jm : Float32} (h : is_positive_float tj = true) :
    (decrE p tj Jm).end_time = p.end_time + tj ∧
    (decrE p tj Jm).end_accel = p.end_accel - Jm * (0.5 : Float32) * tj + Jm * tj ∧
    (decrE p tj Jm).end_vel = p.end_vel - vtF tj Jm + (p.end_accel - Jm * (0.5 : Float32) * tj) * tj +
      Jm * sq_float tj ∧
    (decrE p tj Jm).end_pos = p.end_pos - ptF tj Jm + (p.end_vel - vtF tj Jm) * tj +
      (0.5 : Float32) * (p.end_accel - Jm * (0.5 : Float32) * tj) * sq_float tj + p2tF tj Jm ∧
    (decrE p tj Jm).seg_type = .NEGATIVE_JERK ∧ (decrE p tj Jm).jerk_ref = Jm := by
  rw [decrE, ite_eq_left h]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem constE_pos {p : SCurve.segment_t} {tin J0 : Float32} (h : is_positive_float tin = true) :
    (constE p tin J0).end_time = p.end_time + tin ∧
    (constE p tin J0).end_accel = p.end_accel + J0 * tin ∧
    (constE p tin J0).end_vel = p.end_vel + p.end_accel * tin + (0.5 : Float32) * J0 * sq_float tin ∧
    (constE p tin J0).end_pos = p.end_pos + p.end_vel * tin + (0.5 : Float32) * p.end_accel *
      sq_float tin + (1.0 : Float32) / (6.0 : Float32) * J0 * Float32.pow tin (3.0 : Float32) ∧
    (constE p tin J0).seg_type = .CONSTANT_JERK ∧ (constE p tin J0).jerk_ref = J0 := by
  rw [constE, ite_eq_left h]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

theorem constE_neg {p : SCurve.segment_t} {tin J0 : Float32} (h : is_positive_float tin = false) :
    (constE p tin J0).end_time = p.end_time ∧ (constE p tin J0).end_accel = p.end_accel ∧
    (constE p tin J0).end_vel = p.end_vel ∧ (constE p tin J0).end_pos = p.end_pos ∧
    (constE p tin J0).seg_type = .CONSTANT_JERK ∧ (constE p tin J0).jerk_ref = J0 := by
  rw [constE, ite_eq_right (by rw [h]; exact Bool.false_ne_true)]; exact ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## The steps -/

theorem near_incr {p : SCurve.segment_t} {t : ℝ} {n : SC.Node}
    {eT eA eV eP TM AM VM PM cA cV cP : ℝ} {tj Jm : Float32} (hp : Near p t n eT eA eV eP)
    (hpos : is_positive_float tj = true) (ft : tj.IsFinite) (ht0 : 0 ≤ tj.toReal)
    (ht1 : tj.toReal ≤ 1 / 4) (hTM : |t + tj.toReal| ≤ TM) (hcap : TM ≤ 2 ^ 20) (heT : eT ≤ 1)
    (hmA : |n.a| + eA ≤ AM) (hmV : |n.v| + eV ≤ VM) (hmP : |n.p| + eP ≤ PM)
    (hF : |p.end_accel.toReal| ≤ AM → |p.end_vel.toReal| ≤ VM → |p.end_pos.toReal| ≤ PM →
      A32 (p.end_accel + Jm * (0.5 : Float32) * tj)
        (SC.incrNode (fnode p) Jm.toReal (Real.pi / tj.toReal) tj.toReal).a cA ∧
      A32 (p.end_vel + p.end_accel * tj + vtF tj Jm)
        (SC.incrNode (fnode p) Jm.toReal (Real.pi / tj.toReal) tj.toReal).v cV ∧
      A32 (p.end_pos + p.end_vel * tj + (0.5 : Float32) * p.end_accel * sq_float tj + ptF tj Jm)
        (SC.incrNode (fnode p) Jm.toReal (Real.pi / tj.toReal) tj.toReal).p cP) :
    Near (incrE p tj Jm) (t + tj.toReal) (SC.incrNode n Jm.toReal (Real.pi / tj.toReal) tj.toReal)
      (eT + (TM + eT) / 16777216 + 1 / 10 ^ 40) (eA + cA) (eV + 1 / 4 * eA + cV)
      (eP + 1 / 4 * eV + (1 / 4) ^ 2 / 2 * eA + cP) := by
  obtain ⟨m1, m2, m3⟩ := near_mag hp hmA hmV hmP
  obtain ⟨e1, e2, e3, e4, -, -⟩ := incrE_pos (p := p) (Jm := Jm) hpos
  have F := hF m1 m2 m3
  rw [← e2, ← e3, ← e4] at F
  have hT := near_time hp.1 ft hTM hcap heT
  rw [← e1] at hT
  exact near_of_float (X := fun m => SC.incrNode m Jm.toReal (Real.pi / tj.toReal) tj.toReal) hp
    (lin_incr _ _ _) ht0 ht1 hT F

theorem near_decr {p : SCurve.segment_t} {t : ℝ} {n : SC.Node}
    {eT eA eV eP TM AM VM PM cA cV cP : ℝ} {tj Jm : Float32} (hp : Near p t n eT eA eV eP)
    (hpos : is_positive_float tj = true) (ft : tj.IsFinite) (ht0 : 0 ≤ tj.toReal)
    (ht1 : tj.toReal ≤ 1 / 4) (hTM : |t + tj.toReal| ≤ TM) (hcap : TM ≤ 2 ^ 20) (heT : eT ≤ 1)
    (hmA : |n.a| + eA ≤ AM) (hmV : |n.v| + eV ≤ VM) (hmP : |n.p| + eP ≤ PM)
    (hF : |p.end_accel.toReal| ≤ AM → |p.end_vel.toReal| ≤ VM → |p.end_pos.toReal| ≤ PM →
      A32 (p.end_accel - Jm * (0.5 : Float32) * tj + Jm * tj)
        (SC.decrNode (fnode p) Jm.toReal (Real.pi / tj.toReal) tj.toReal).a cA ∧
      A32 (p.end_vel - vtF tj Jm + (p.end_accel - Jm * (0.5 : Float32) * tj) * tj + Jm * sq_float tj)
        (SC.decrNode (fnode p) Jm.toReal (Real.pi / tj.toReal) tj.toReal).v cV ∧
      A32 (p.end_pos - ptF tj Jm + (p.end_vel - vtF tj Jm) * tj +
          (0.5 : Float32) * (p.end_accel - Jm * (0.5 : Float32) * tj) * sq_float tj + p2tF tj Jm)
        (SC.decrNode (fnode p) Jm.toReal (Real.pi / tj.toReal) tj.toReal).p cP) :
    Near (decrE p tj Jm) (t + tj.toReal) (SC.decrNode n Jm.toReal (Real.pi / tj.toReal) tj.toReal)
      (eT + (TM + eT) / 16777216 + 1 / 10 ^ 40) (eA + cA) (eV + 1 / 4 * eA + cV)
      (eP + 1 / 4 * eV + (1 / 4) ^ 2 / 2 * eA + cP) := by
  obtain ⟨m1, m2, m3⟩ := near_mag hp hmA hmV hmP
  obtain ⟨e1, e2, e3, e4, -, -⟩ := decrE_pos (p := p) (Jm := Jm) hpos
  have F := hF m1 m2 m3
  rw [← e2, ← e3, ← e4] at F
  have hT := near_time hp.1 ft hTM hcap heT
  rw [← e1] at hT
  exact near_of_float (X := fun m => SC.decrNode m Jm.toReal (Real.pi / tj.toReal) tj.toReal) hp
    (lin_decr _ _ _) ht0 ht1 hT F

theorem near_const {p : SCurve.segment_t} {t : ℝ} {n : SC.Node}
    {eT eA eV eP TM AM VM PM cA cV cP D : ℝ} {tin J0 : Float32} (hp : Near p t n eT eA eV eP)
    (hpos : is_positive_float tin = true) (ft : tin.IsFinite) (ht0 : 0 ≤ tin.toReal)
    (ht1 : tin.toReal ≤ D) (hTM : |t + tin.toReal| ≤ TM) (hcap : TM ≤ 2 ^ 20) (heT : eT ≤ 1)
    (hmA : |n.a| + eA ≤ AM) (hmV : |n.v| + eV ≤ VM) (hmP : |n.p| + eP ≤ PM)
    (hF : |p.end_accel.toReal| ≤ AM → |p.end_vel.toReal| ≤ VM → |p.end_pos.toReal| ≤ PM →
      A32 (p.end_accel + J0 * tin) (SC.constNode (fnode p) J0.toReal tin.toReal).a cA ∧
      A32 (p.end_vel + p.end_accel * tin + (0.5 : Float32) * J0 * sq_float tin)
        (SC.constNode (fnode p) J0.toReal tin.toReal).v cV ∧
      A32 (p.end_pos + p.end_vel * tin + (0.5 : Float32) * p.end_accel * sq_float tin +
          (1.0 : Float32) / (6.0 : Float32) * J0 * Float32.pow tin (3.0 : Float32))
        (SC.constNode (fnode p) J0.toReal tin.toReal).p cP) :
    Near (constE p tin J0) (t + tin.toReal) (SC.constNode n J0.toReal tin.toReal)
      (eT + (TM + eT) / 16777216 + 1 / 10 ^ 40) (eA + cA) (eV + D * eA + cV)
      (eP + D * eV + D ^ 2 / 2 * eA + cP) := by
  obtain ⟨m1, m2, m3⟩ := near_mag hp hmA hmV hmP
  obtain ⟨e1, e2, e3, e4, -, -⟩ := constE_pos (p := p) (J0 := J0) hpos
  have F := hF m1 m2 m3
  rw [← e2, ← e3, ← e4] at F
  have hT := near_time hp.1 ft hTM hcap heT
  rw [← e1] at hT
  exact near_of_float (X := fun m => SC.constNode m J0.toReal tin.toReal) hp
    (lin_const _ _) ht0 ht1 hT F

theorem constNode_zero_d (n : SC.Node) (J : ℝ) : SC.constNode n J 0 = n := by
  cases n; simp [SC.constNode, SC.cA, SC.cV, SC.cP]

/-- A gated (zero-duration) constant segment copies the entry. -/
theorem near_gated {p : SCurve.segment_t} {t : ℝ} {n : SC.Node} {eT eA eV eP : ℝ} {tin J0 : Float32}
    (hp : Near p t n eT eA eV eP) (hneg : is_positive_float tin = false) (J : ℝ) :
    Near (constE p tin J0) (t + 0) (SC.constNode n J 0) eT eA eV eP := by
  obtain ⟨e1, e2, e3, e4, -, -⟩ := constE_neg (p := p) (J0 := J0) hneg
  rw [constNode_zero_d, add_zero]
  exact ⟨e1 ▸ hp.1, e2 ▸ hp.2.1, e3 ▸ hp.2.2.1, e4 ▸ hp.2.2.2⟩

theorem near_const0 {p : SCurve.segment_t} {t : ℝ} {n : SC.Node}
    {eT eA eV eP TM AM VM PM cV cP D : ℝ} {tin : Float32} (hp : Near p t n eT eA eV eP)
    (hpos : is_positive_float tin = true) (ft : tin.IsFinite) (ht0 : 0 ≤ tin.toReal)
    (ht1 : tin.toReal ≤ D) (hTM : |t + tin.toReal| ≤ TM) (hcap : TM ≤ 2 ^ 20) (heT : eT ≤ 1)
    (hmA : |n.a| + eA ≤ AM) (hmV : |n.v| + eV ≤ VM) (hmP : |n.p| + eP ≤ PM)
    (hF : |p.end_accel.toReal| ≤ AM → |p.end_vel.toReal| ≤ VM → |p.end_pos.toReal| ≤ PM →
      A32 (p.end_accel + (0.0 : Float32) * tin) (SC.constNode (fnode p) 0 tin.toReal).a 0 ∧
      A32 (p.end_vel + p.end_accel * tin + (0.5 : Float32) * (0.0 : Float32) * sq_float tin)
        (SC.constNode (fnode p) 0 tin.toReal).v cV ∧
      A32 (p.end_pos + p.end_vel * tin + (0.5 : Float32) * p.end_accel * sq_float tin +
          (1.0 : Float32) / (6.0 : Float32) * (0.0 : Float32) * Float32.pow tin (3.0 : Float32))
        (SC.constNode (fnode p) 0 tin.toReal).p cP) :
    Near (constE p tin 0.0) (t + tin.toReal) (SC.constNode n 0 tin.toReal)
      (eT + (TM + eT) / 16777216 + 1 / 10 ^ 40) (eA + 0) (eV + D * eA + cV)
      (eP + D * eV + D ^ 2 / 2 * eA + cP) := by
  obtain ⟨m1, m2, m3⟩ := near_mag hp hmA hmV hmP
  obtain ⟨e1, e2, e3, e4, -, -⟩ := constE_pos (p := p) (J0 := 0.0) hpos
  have F := hF m1 m2 m3
  rw [← e2, ← e3, ← e4] at F
  have hT := near_time hp.1 ft hTM hcap heT
  rw [← e1] at hT
  exact near_of_float (X := fun m => SC.constNode m 0 tin.toReal) hp
    (lin_const _ _) ht0 ht1 hT F

theorem eff_pos {x : Float32} (fx : x.IsFinite) (h : is_positive_float x = true) :
    eff x.toReal = x.toReal ∧ 1 / 2 ^ 23 ≤ x.toReal := by
  have h1 := (wp_isPos_iff fx).1 h
  have h2 : (1 / 2 ^ 23 : ℝ) ≤ x.toReal := by
    have : (2 : ℝ) ^ (-23 : ℤ) = 1 / 2 ^ 23 := by norm_num
    rw [this] at h1; exact h1
  exact ⟨by unfold eff; rw [ite_eq_left h2], h2⟩

theorem eff_neg {x : Float32} (fx : x.IsFinite) (h : is_positive_float x = false) :
    eff x.toReal = 0 ∧ x.toReal < 1 / 2 ^ 23 := by
  have h1 : ¬ 2 ^ (-23 : ℤ) ≤ x.toReal := fun hc => by
    rw [← wp_isPos_iff fx] at hc; rw [hc] at h; exact Bool.noConfusion h
  have h2 : x.toReal < 1 / 2 ^ 23 := by
    have : (2 : ℝ) ^ (-23 : ℤ) = 1 / 2 ^ 23 := by norm_num
    rw [this] at h1; exact not_le.1 h1
  exact ⟨by unfold eff; rw [ite_eq_right (not_le.2 h2)], h2⟩

theorem mag_a {a e AM : ℝ} (h : |a| ≤ 2) (he : 2 + e ≤ AM) : |a| + e ≤ AM := by linarith

theorem mag_v {v e X VM : ℝ} (h0 : 0 ≤ v) (h1 : v ≤ X) (he : X + e ≤ VM) : |v| + e ≤ VM := by
  rw [abs_of_nonneg h0]; linarith

theorem mag_t {t X TM : ℝ} (h0 : 0 ≤ t) (h1 : t ≤ X) (hX : X ≤ TM) : |t| ≤ TM := by
  rw [abs_of_nonneg h0]; linarith

theorem Near.zeroA {e : SCurve.segment_t} {t : ℝ} {n : SC.Node} {eT eA eV eP : ℝ}
    (h : Near e t n eT eA eV eP) (hn : n.a = 0) :
    Near { e with end_accel := 0.0 } t n eT 0 eV eP :=
  ⟨h.1, ⟨f32_isFinite_0p0, by rw [f32_toReal_0p0, hn]; simp⟩, h.2.2.1, h.2.2.2⟩

theorem Near.zeroAV {e : SCurve.segment_t} {t : ℝ} {n : SC.Node} {eT eA eV eP : ℝ}
    (h : Near e t n eT eA eV eP) (ha : n.a = 0) (hv : n.v = 0) :
    Near { e with end_accel := 0.0, end_vel := 0.0 } t n eT 0 0 eP :=
  ⟨h.1, ⟨f32_isFinite_0p0, by rw [f32_toReal_0p0, ha]; simp⟩,
    ⟨f32_isFinite_0p0, by rw [f32_toReal_0p0, hv]; simp⟩, h.2.2.2⟩

end SCT

end

end Contracts.Mission
