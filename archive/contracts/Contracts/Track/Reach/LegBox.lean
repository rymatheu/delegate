import Contracts.Track.Reach.LegHold
import Contracts.Track.Induction.Pieces

/-!
# The leg theorem inside a box: the loiter target from `loiter_dest_bound` (REACH.md §9)

`waypoint_reach_h_box`: `waypoint_reach_h` for a hover point and a waypoint inside a box
(`|p₀ i| ≤ 1.5`, `|w' i| ≤ 1.9` per axis), with `LegFacts` replaced by `LegFactsBox`, in which the
`loiter` sub-field (the loiter target's distance bound) is not assumed: it is proved from the
code's stopping point by `Mission.loiter_dest_bound`. What remains in its place is the code-level
fact that the loiter target is the stopping point of the position controller's state at the
completion tick (`LoiterHyps` of that state, its estimates being the sample: within `10⁻⁶` of the
plant state), the form of INDUCTION's `loiter_nav`.

**The box.** `loiter_dest_bound` needs the position estimate within 2 m of the origin per axis (its
`float` rounding allowance `10⁻⁵`). At completion the vehicle is within `0.08` of `w'`, so the
estimate is within `1.9 + 0.08 + 10⁻⁶ ≤ 2` per axis when `|w' i| ≤ 1.9`. The brief's
`|p₀ i| ≤ 1.5` with `hR` gives only `|w' i| ≤ 5.1`, so the waypoint bound is a separate hypothesis
(`hw`); `_hbox` is kept as asked, unused by the proof.
-/

namespace Contracts.Track.Reach.Leg

open Contracts Contracts.STL Contracts.Mission Matrix Finset Contracts.Track.Induction
  Contracts.Track.Reach.Glue

noncomputable section

/-- **The navigator's phases, with the loiter target as the code's stopping point** (`LegPhase`
without `loiter`, with `loiterCode`). -/
structure LegPhaseBox (w₀ : Vehicle.World) (w' : P3) (x : ℕ → X) (Tc Tl : ℕ) :
    Prop where
  order : ts ≤ Tc ∧ Tc ≤ Tl ∧ Tl ≤ Tc + 450
  legV : ∀ t, ts ≤ t → t < Tc → |aZ w₀ x t| ≤ 1 / 1000 ∧ |d1Z w₀ x t| ≤ 1 / 10 ^ 8 ∧
    |d2Z w₀ x t| ≤ 1 / 10 ^ 7
  hold : ∀ t, Tl ≤ t → posTarget (x t) = posTarget (x Tl) ∧
    ∀ i, |velTarget (x t) i| ≤ 1 / 10 ^ 6 ∧ |accDes w₀ x t i| ≤ 1 / 10 ^ 6
  arrive : ∃ Te, ts ≤ Te ∧ Te ≤ 2200 ∧
    (∀ t, Te ≤ t → t < Tc → dist (posTarget (x t)) w' ≤ 1 / 1000 ∧
      ∀ a, |aH w₀ x t a| ≤ 1 / 10 ^ 6 ∧ |d1H w₀ x t a| ≤ 1 / 10 ^ 8 ∧
        |d2H w₀ x t a| ≤ 3 / 10 ^ 6) ∧
    ∀ t, Te ≤ t → t < Tc → dist (pos (x t)) w' ≤ 99 / 1000 → Tc ≤ t + 1
  atComplete : dist (pos (x Tc)) w' + ‖vel (x Tc)‖ ≤ 8 / 100
  /-- **The loiter target is the stopping point** (`loiter_start` at the completion tick sets the
  destination to `get_wp_stopping_point_NED_m` of the position controller's state `s`, whose
  estimates are the tick's sample; the loiter S-curve ends at it within `10⁻⁶`). -/
  loiterCode : ∃ (p : AC_PosControl_lib.AC_PosControl.Params) (s : AC_PosControl_lib.AC_PosControl.State),
    LoiterHyps p s ∧
    dist (estPos s) (pos (x Tc)) ≤ 1 / 10 ^ 6 ∧ dist (estVel s) (vel (x Tc)) ≤ 1 / 10 ^ 6 ∧
    dist (posTarget (x Tl)) (stopPt p s) ≤ 1 / 10 ^ 6

/-- The per-tick facts of one behavior, with `LegPhaseBox`. -/
structure LegRunBox (w₀ : Vehicle.World) (w' : P3) (x : ℕ → X) : Prop where
  init : (∀ j, |ξV w₀ x ts j| ≤ ε0VL j) ∧ (∀ a j, |ξH w₀ x ts a j| ≤ ε0HL j) ∧
    (∀ a, |aH w₀ x ts a| ≤ 1 / 1000) ∧ ∀ a, |d2H w₀ x ts a| ≤ 1 / 10 ^ 6
  tick : ∀ t, ts ≤ t → t < hzn → (∀ k, ts ≤ k → k ≤ t → BoxL (ξV w₀ x) (ξH w₀ x) k) →
    TickBounds (ξV w₀ x) (legWV w₀ x) (aZ w₀ x) (d1Z w₀ x) (d2Z w₀ x) (ξH w₀ x) (legWH w₀ x)
      (aH w₀ x) (d1H w₀ x) (d2H w₀ x) t
  d2sum : ∀ N, ts + N ≤ hzn → (∀ k, ts ≤ k → k ≤ ts + N → BoxL (ξV w₀ x) (ξH w₀ x) k) → ∀ a,
    ∑ k ∈ Finset.range N, |d2H w₀ x (ts + k) a| ≤ 1 / 4
  phase : ∃ Tc Tl : ℕ, LegPhaseBox w₀ w' x Tc Tl

/-- **The facts of the leg inside the box**: `LegFacts` without the `loiter` sub-field. -/
structure LegFactsBox (sense32 : ℝ → Float32) (senseP : ℝ → Float) (w₀ : Vehicle.World) (p₀ : P3)
    (w' : AC_WPNav_lib.Vector3p.State) (ψ₀ : ℝ) : Prop where
  run : ∀ x ∈ Mloop sense32 senseP w₀ ∩ Reach.Ahover p₀ ψ₀, LegRunBox w₀ (wpt w') x

/-- **The loiter target from the code** (`loiter_dest_bound`): inside the box, the stopping point
of the completion tick is within `dist + ‖v‖ + 10⁻³` of `w'` (from the state at completion and the
code-level loiter fact alone; used by the 3D theorem too). -/
theorem loiter_of_code' (hL : LibmSpec) {w' : P3} {x : ℕ → X}
    (hw : ∀ i, |w' i| ≤ 19 / 10) {Tc Tl : ℕ}
    (hc : dist (pos (x Tc)) w' + ‖vel (x Tc)‖ ≤ 8 / 100)
    (hcode : ∃ (p : AC_PosControl_lib.AC_PosControl.Params)
      (s : AC_PosControl_lib.AC_PosControl.State), LoiterHyps p s ∧
      dist (estPos s) (pos (x Tc)) ≤ 1 / 10 ^ 6 ∧ dist (estVel s) (vel (x Tc)) ≤ 1 / 10 ^ 6 ∧
      dist (posTarget (x Tl)) (stopPt p s) ≤ 1 / 10 ^ 6) :
    dist (posTarget (x Tl)) w' ≤ dist (pos (x Tc)) w' + ‖vel (x Tc)‖ + 1 / 1000 := by
  obtain ⟨p, s, hH, hp, hv, ht⟩ := hcode
  have hd0 := dist_nonneg (x := pos (x Tc)) (y := w')
  have hn0 := norm_nonneg (vel (x Tc))
  have hdE : dist (estPos s) w' ≤ dist (pos (x Tc)) w' + 1 / 10 ^ 6 := by
    have := dist_triangle (estPos s) (pos (x Tc)) w'; linarith
  have hvE : ‖estVel s‖ ≤ ‖vel (x Tc)‖ + 1 / 10 ^ 6 := by
    have := norm_le_norm_add_norm_sub' (estVel s) (vel (x Tc))
    rw [← dist_eq_norm] at this; linarith
  have hco : ∀ i : Fin 3, |estPos s i| ≤ 2 := fun i => by
    have h1 := abs_coord_le_dist (estPos s) w' i
    have h2 := abs_sub_abs_le_abs_sub (estPos s i) (w' i)
    have h3 := hw i
    linarith
  have c0 := hco 0
  have c1 := hco 1
  have c2 := hco 2
  simp only [estPos] at c0 c1 c2
  simp at c0 c1 c2
  have hb := loiter_dest_bound hL p s hH.hkp hH.hacc hH.hvm hH.hkpd hH.haccd hH.hpox hH.hpoy
    hH.hpoz hH.hvox hH.hvoy hH.hvoz hH.hpx hH.hpy hH.hpz c0 c1 c2 hH.hvx hH.hvy hH.hvz
    (by linarith) w'
  have := dist_triangle (posTarget (x Tl)) (stopPt p s) w'
  linarith

/-- **The loiter target from the code** for `LegPhaseBox`. -/
theorem loiter_of_code (hL : LibmSpec) {w₀ : Vehicle.World} {w' : P3} {x : ℕ → X}
    (hw : ∀ i, |w' i| ≤ 19 / 10) {Tc Tl : ℕ} (hP : LegPhaseBox w₀ w' x Tc Tl) :
    dist (posTarget (x Tl)) w' ≤ dist (pos (x Tc)) w' + ‖vel (x Tc)‖ + 1 / 1000 :=
  loiter_of_code' hL hw hP.atComplete hP.loiterCode

/-- `LegPhaseBox` gives `LegPhase` inside the box. -/
theorem legPhase_of_box (hL : LibmSpec) {w₀ : Vehicle.World} {w' : P3} {x : ℕ → X}
    (hw : ∀ i, |w' i| ≤ 19 / 10) {Tc Tl : ℕ} (hP : LegPhaseBox w₀ w' x Tc Tl) :
    LegPhase w₀ w' x Tc Tl where
  order := hP.order
  legV := hP.legV
  hold := hP.hold
  arrive := hP.arrive
  atComplete := hP.atComplete
  loiter := loiter_of_code hL hw hP

/-- `LegFactsBox` gives `LegFacts` inside the box. -/
theorem legFacts_of_box {sense32 : ℝ → Float32} {senseP : ℝ → Float} {w₀ : Vehicle.World}
    {p₀ : P3} {w' : AC_WPNav_lib.Vector3p.State} {ψ₀ : ℝ} (hL : LibmSpec)
    (hw : ∀ i, |wpt w' i| ≤ 19 / 10) (hF : LegFactsBox sense32 senseP w₀ p₀ w' ψ₀) :
    LegFacts sense32 senseP w₀ p₀ w' ψ₀ where
  run x hx := by
    obtain ⟨hi, ht, hs, ⟨Tc, Tl, hP⟩⟩ := hF.run x hx
    exact ⟨hi, ht, hs, ⟨Tc, Tl, legPhase_of_box hL hw hP⟩⟩

/-- **The leg theorem inside the box**, with the loiter target discharged from
`loiter_dest_bound`. -/
theorem waypoint_reach_h_box (sense32 : ℝ → Float32) (senseP : ℝ → Float) (w₀ : Vehicle.World)
    (p₀ : P3) (w' : AC_WPNav_lib.Vector3p.State) (ψ₀ : ℝ) (hP : LegParams w₀)
    (hmin : 1 / 100 ≤ dist p₀ (wpt w')) (hR : dist p₀ (wpt w') ≤ 36 / 10) (hZ : wpt w' 2 = p₀ 2)
    (_hbox : ∀ i, |p₀ i| ≤ 3 / 2) (hw : ∀ i, |wpt w' i| ≤ 19 / 10)
    (hW : ReachWorld w₀ w') (hS : Plant.CopterSense sense32 senseP) (hL : LibmSpec)
    (hF : LegFactsBox sense32 senseP w₀ p₀ w' ψ₀) :
    Mloop sense32 senseP w₀ ⊨
      ⟨Ahover p₀ ψ₀, lang_t 0 (.eventually 0 4800 (.always 0 1200 (near (wpt w') (1 / 10))))⟩ :=
  waypoint_reach_h sense32 senseP w₀ p₀ w' ψ₀ hP hmin hR hZ hW hS hL (legFacts_of_box hL hw hF)

end

end Contracts.Track.Reach.Leg
