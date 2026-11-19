import Contracts.Track.Reach.Leg3Nav

/-!
# The 3D leg theorem, the hold and the assembly (REACH.md §10)

* `err_hold3`: from `Mt3 = 2624` ticks after `Tl` to the horizon, the vehicle is within `0.0184` of
  the loiter point (horizontal tails past `Mt = 1728`, vertical tails past `Mt3`, the velocity
  defects through their sums over the run and the peaks of the tails, the full gains on the residual
  forcing of the hold, and the tube).
* `waypoint_reach`: **the 3D leg theorem**. The window starts at `Tl + 2624 ≤ 2905 + 450 + 2624 =
  5979 ≤ 6000`; on it `‖p − w'‖ ≤ 0.0184 + 0.081 = 0.0994 ≤ 0.1`.
-/

namespace Contracts.Track.Reach.Leg3

open Contracts Contracts.STL Contracts.Mission Matrix Finset Contracts.Track.Induction
  Contracts.Track.Reach.Glue Contracts.Track.Reach.Leg

noncomputable section

variable {w₀ : Vehicle.World} {w' : P3} {x : ℕ → X}

theorem target_held3 {Tc Tl : ℕ} (hP : LegPhase3 w₀ w' x Tc Tl) (t : ℕ) (ht : Tl ≤ t) :
    posTarget (x t) = posTarget (x Tl) := (hP.hold t ht).1

/-- After the loiter, the horizontal reference forcing is below `10⁻⁶`, `3·10⁻⁹`, `3·10⁻⁶`. -/
theorem forcing_small_H3 {Tc Tl : ℕ} (hP : LegPhase3 w₀ w' x Tc Tl) (a : Fin 2) (t : ℕ)
    (ht : Tl ≤ t) :
    |aH w₀ x t a| ≤ 1 / 10 ^ 6 ∧ |d1H w₀ x t a| ≤ 3 / 10 ^ 9 ∧ |d2H w₀ x t a| ≤ 3 / 10 ^ 6 := by
  obtain ⟨p0, h0⟩ := hP.hold t ht
  obtain ⟨p1, h1⟩ := hP.hold (t + 1) (by omega)
  have v0 := (h0 a.castSucc).1
  have a0 := (h0 a.castSucc).2
  have v1 := (h1 a.castSucc).1
  have hp : posTarget (x (t + 1)) a.castSucc = posTarget (x t) a.castSucc := by rw [p1, p0]
  refine ⟨?_, ?_, ?_⟩
  · simpa [aH, refH, refAx] using a0
  · simp only [d1H, refH, refAx, Horizontal.defect₁, hp, per_le]
    rw [abs_le] at v0 a0 ⊢
    constructor <;> nlinarith [v0.1, v0.2, a0.1, a0.2]
  · simp only [d2H, refH, refAx, Horizontal.defect₂, per_le]
    rw [abs_le] at v0 v1 a0 ⊢
    constructor <;> nlinarith [v0.1, v0.2, v1.1, v1.2, a0.1, a0.2]

/-- After the loiter, the vertical reference forcing is below `10⁻⁶`, `3·10⁻⁹`, `3·10⁻⁶`. -/
theorem forcing_small_V3 {Tc Tl : ℕ} (hP : LegPhase3 w₀ w' x Tc Tl) (t : ℕ) (ht : Tl ≤ t) :
    |aZ w₀ x t| ≤ 1 / 10 ^ 6 ∧ |d1Z w₀ x t| ≤ 3 / 10 ^ 9 ∧ |d2Z w₀ x t| ≤ 3 / 10 ^ 6 := by
  obtain ⟨p0, h0⟩ := hP.hold t ht
  obtain ⟨p1, h1⟩ := hP.hold (t + 1) (by omega)
  have v0 := (h0 2).1
  have a0 := (h0 2).2
  have v1 := (h1 2).1
  have hp : posTarget (x (t + 1)) 2 = posTarget (x t) 2 := by rw [p1, p0]
  refine ⟨?_, ?_, ?_⟩
  · simpa [aZ, refV, refAx] using a0
  · simp only [d1Z, refV, refAx, Vertical.defect₁, hp, perV_le]
    rw [abs_le] at v0 a0 ⊢
    constructor <;> nlinarith [v0.1, v0.2, a0.1, a0.2]
  · simp only [d2Z, refV, refAx, Vertical.defect₂, perV_le]
    rw [abs_le] at v0 v1 a0 ⊢
    constructor <;> nlinarith [v0.1, v0.2, v1.1, v1.2, a0.1, a0.2]

/-- **The hold in 3D**: from `Tl + Mt3` to the horizon the vehicle is within `0.0184` of the
target. -/
theorem err_hold3 (hx : LegRun3 w₀ w' x) {Tc Tl : ℕ} (hP : LegPhase3 w₀ w' x Tc Tl) (t : ℕ)
    (h1 : Tl + Mt3 ≤ t) (h2 : t ≤ hzn3) :
    err (x t) ≤ 184 / 10000 := by
  have hM := legModel3_of_run hx
  have hts : ts ≤ Tl := hP.order.1.trans hP.order.2.1
  have eMt : Mt = 1728 := rfl
  have eMt3 : Mt3 = 2624 := rfl
  obtain ⟨N, rfl⟩ : ∃ N, t = ts + N := ⟨t - ts, by omega⟩
  have hS := d2sum_run3 hx N h2
  have e0 := tail_e3 hM refGains_certified refGains3_certified Tl 0 (forcing_small_H3 hP 0) N
    (hS.1 0) (by omega) h2
  have e1 := tail_e3 hM refGains_certified refGains3_certified Tl 1 (forcing_small_H3 hP 1) N
    (hS.1 1) (by omega) h2
  have ez := tail_z3 hM refGains_certified refGains3_certified Tl (forcing_small_V3 hP) N hS.2
    h1 h2
  rw [Leg.err_eq, Real.sqrt_le_left (by norm_num)]
  exact hold3_3d e0 e1 ez

/-- **The 3D leg theorem** at `PSC_D_ACC_P 0.25`: from a hover at `p₀` (any heading `ψ₀`), one
waypoint `w'` in any direction between 1 cm and 3.6 m away: within 6000 ticks the vehicle is within
`0.1` of `w'` for 1200 consecutive ticks. -/
theorem waypoint_reach (sense32 : ℝ → Float32) (senseP : ℝ → Float) (w₀ : Vehicle.World)
    (p₀ : P3) (w' : AC_WPNav_lib.Vector3p.State) (ψ₀ : ℝ) (hP : LegParams3 w₀)
    (hmin : 1 / 100 ≤ dist p₀ (wpt w')) (hR : dist p₀ (wpt w') ≤ 36 / 10)
    (hW : ReachWorld w₀ w') (hS : Plant.CopterSense sense32 senseP) (hL : LibmSpec)
    (hF : LegFacts3 sense32 senseP w₀ p₀ w' ψ₀) :
    Mloop sense32 senseP w₀ ⊨
      ⟨Ahover p₀ ψ₀, lang_t 0 (.eventually 0 6000 (.always 0 1200 (near (wpt w') (1 / 10))))⟩ := by
  rintro x ⟨hx, hA⟩
  have hrun := hF.run x ⟨hx, hA⟩
  obtain ⟨Tc, Tl, hP⟩ := hrun.phase
  have hTc := Tc_le3 hrun hP
  have hTl := hP.order.2.2
  have hL' := loiter_near3 hP
  have eM : Mt3 = 2624 := rfl
  have eMc : Mc3 = 704 := rfl
  have eH : hzn3 = 7200 := rfl
  simp only [mem_lang_t, sat_eventually, sat_always, sat_near]
  refine ⟨Tl + Mt3, by omega, by omega, fun τ h1 h2 => ?_⟩
  have hE := err_hold3 hrun hP τ (by omega) (by omega)
  have hT := target_held3 hP τ (by omega)
  have := dist_triangle (pos (x τ)) (posTarget (x τ)) (wpt w')
  rw [hT] at this
  have : err (x τ) = dist (pos (x τ)) (posTarget (x τ)) := rfl
  rw [hT] at this
  linarith

end

end Contracts.Track.Reach.Leg3
