import Contracts.Track.Reach.Leg3Hold
import Contracts.Track.Reach.LegBox

/-!
# The 3D leg theorem inside a box: the loiter target from `loiter_dest_bound` (REACH.md §10)

`waypoint_reach_box`: `waypoint_reach` for a hover point and a waypoint inside a box
(`|p₀ i| ≤ 1.5`, `|w' i| ≤ 1.9` per axis), with `LegFacts3` replaced by `LegFactsBox3`, in which
the `loiter` sub-field is proved from the code's stopping point (`Leg.loiter_of_code`'s argument,
`Mission.loiter_dest_bound`), as in LegBox.lean.
-/

namespace Contracts.Track.Reach.Leg3

open Contracts Contracts.STL Contracts.Mission Matrix Finset Contracts.Track.Induction
  Contracts.Track.Reach.Glue Contracts.Track.Reach.Leg

noncomputable section

/-- `LegPhase3` without `loiter`, with `loiterCode`. -/
structure LegPhaseBox3 (w₀ : Vehicle.World) (w' : P3) (x : ℕ → X) (Tc Tl : ℕ) : Prop where
  order : ts ≤ Tc ∧ Tc ≤ Tl ∧ Tl ≤ Tc + 450
  hold : ∀ t, Tl ≤ t → posTarget (x t) = posTarget (x Tl) ∧
    ∀ i, |velTarget (x t) i| ≤ 1 / 10 ^ 6 ∧ |accDes w₀ x t i| ≤ 1 / 10 ^ 6
  arrive : ∃ Te, ts ≤ Te ∧ Te ≤ 2200 ∧
    (∀ t, Te ≤ t → t < Tc → dist (posTarget (x t)) w' ≤ 1 / 1000 ∧
      (∀ a, |aH w₀ x t a| ≤ 1 / 10 ^ 6 ∧ |d1H w₀ x t a| ≤ 1 / 10 ^ 8 ∧
        |d2H w₀ x t a| ≤ 3 / 10 ^ 6) ∧
      |aZ w₀ x t| ≤ 1 / 10 ^ 6 ∧ |d1Z w₀ x t| ≤ 1 / 10 ^ 8 ∧ |d2Z w₀ x t| ≤ 3 / 10 ^ 6) ∧
    ∀ t, Te ≤ t → t < Tc → dist (pos (x t)) w' ≤ 99 / 1000 → Tc ≤ t + 1
  atComplete : dist (pos (x Tc)) w' + ‖vel (x Tc)‖ ≤ 8 / 100
  /-- **The loiter target is the stopping point** of the completion tick's position controller. -/
  loiterCode : ∃ (p : AC_PosControl_lib.AC_PosControl.Params) (s : AC_PosControl_lib.AC_PosControl.State),
    LoiterHyps p s ∧
    dist (estPos s) (pos (x Tc)) ≤ 1 / 10 ^ 6 ∧ dist (estVel s) (vel (x Tc)) ≤ 1 / 10 ^ 6 ∧
    dist (posTarget (x Tl)) (stopPt p s) ≤ 1 / 10 ^ 6

/-- The per-tick facts of one 3D behavior, with `LegPhaseBox3`. -/
structure LegRunBox3 (w₀ : Vehicle.World) (w' : P3) (x : ℕ → X) : Prop where
  init : (∀ j, |ξV w₀ x ts j| ≤ ε0VL j) ∧ (∀ a j, |ξH w₀ x ts a j| ≤ ε0HL j) ∧
    (∀ a, |aH w₀ x ts a| ≤ 1 / 1000) ∧ |aZ w₀ x ts| ≤ 1 / 1000 ∧ ∀ a, |d2H w₀ x ts a| ≤ 1 / 10 ^ 6
  tick : ∀ t, ts ≤ t → t < hzn3 → (∀ k, ts ≤ k → k ≤ t → BoxL3 (ξV w₀ x) (ξH w₀ x) k) →
    TickBounds3 (ξV w₀ x) (legWV3 w₀ x) (aZ w₀ x) (d1Z w₀ x) (d2Z w₀ x) (ξH w₀ x) (legWH w₀ x)
      (aH w₀ x) (d1H w₀ x) (d2H w₀ x) t
  d2sum : ∀ N, ts + N ≤ hzn3 → (∀ k, ts ≤ k → k ≤ ts + N → BoxL3 (ξV w₀ x) (ξH w₀ x) k) →
    (∀ a, ∑ k ∈ Finset.range N, |d2H w₀ x (ts + k) a| ≤ 1 / 4) ∧
      ∑ k ∈ Finset.range N, |d2Z w₀ x (ts + k)| ≤ 1 / 4
  phase : ∃ Tc Tl : ℕ, LegPhaseBox3 w₀ w' x Tc Tl

/-- **The facts of the 3D leg inside the box**: `LegFacts3` without the `loiter` sub-field. -/
structure LegFactsBox3 (sense32 : ℝ → Float32) (senseP : ℝ → Float) (w₀ : Vehicle.World) (p₀ : P3)
    (w' : AC_WPNav_lib.Vector3p.State) (ψ₀ : ℝ) : Prop where
  run : ∀ x ∈ Mloop sense32 senseP w₀ ∩ Reach.Ahover p₀ ψ₀, LegRunBox3 w₀ (wpt w') x

/-- `LegPhaseBox3` gives `LegPhase3` inside the box (the loiter target from `loiter_dest_bound`,
through the horizontal theorem's `loiter_of_code`). -/
theorem legPhase3_of_box (hL : LibmSpec) {w₀ : Vehicle.World} {w' : P3} {x : ℕ → X}
    (hw : ∀ i, |w' i| ≤ 19 / 10) {Tc Tl : ℕ} (hP : LegPhaseBox3 w₀ w' x Tc Tl) :
    LegPhase3 w₀ w' x Tc Tl where
  order := hP.order
  hold := hP.hold
  arrive := hP.arrive
  atComplete := hP.atComplete
  loiter := loiter_of_code' hL hw hP.atComplete hP.loiterCode

/-- `LegFactsBox3` gives `LegFacts3` inside the box. -/
theorem legFacts3_of_box {sense32 : ℝ → Float32} {senseP : ℝ → Float} {w₀ : Vehicle.World}
    {p₀ : P3} {w' : AC_WPNav_lib.Vector3p.State} {ψ₀ : ℝ} (hL : LibmSpec)
    (hw : ∀ i, |wpt w' i| ≤ 19 / 10) (hF : LegFactsBox3 sense32 senseP w₀ p₀ w' ψ₀) :
    LegFacts3 sense32 senseP w₀ p₀ w' ψ₀ where
  run x hx := by
    obtain ⟨hi, ht, hs, ⟨Tc, Tl, hP⟩⟩ := hF.run x hx
    exact ⟨hi, ht, hs, ⟨Tc, Tl, legPhase3_of_box hL hw hP⟩⟩

/-- **The 3D leg theorem inside the box**, with the loiter target discharged from
`loiter_dest_bound`. -/
theorem waypoint_reach_box (sense32 : ℝ → Float32) (senseP : ℝ → Float) (w₀ : Vehicle.World)
    (p₀ : P3) (w' : AC_WPNav_lib.Vector3p.State) (ψ₀ : ℝ) (hP : LegParams3 w₀)
    (hmin : 1 / 100 ≤ dist p₀ (wpt w')) (hR : dist p₀ (wpt w') ≤ 36 / 10)
    (_hbox : ∀ i, |p₀ i| ≤ 3 / 2) (hw : ∀ i, |wpt w' i| ≤ 19 / 10)
    (hW : ReachWorld w₀ w') (hS : Plant.CopterSense sense32 senseP) (hL : LibmSpec)
    (hF : LegFactsBox3 sense32 senseP w₀ p₀ w' ψ₀) :
    Mloop sense32 senseP w₀ ⊨
      ⟨Ahover p₀ ψ₀, lang_t 0 (.eventually 0 6000 (.always 0 1200 (near (wpt w') (1 / 10))))⟩ :=
  waypoint_reach sense32 senseP w₀ p₀ w' ψ₀ hP hmin hR hW hS hL (legFacts3_of_box hL hw hF)

end

end Contracts.Track.Reach.Leg3
